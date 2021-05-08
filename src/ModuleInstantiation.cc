#include "compiler_specific.h"
#include "context.h"
#include "ModuleInstantiation.h"
#include "expression.h"
#include "exceptions.h"
#include "modcontext.h"
#include "node.h"
#include "printutils.h"
#include "stackcheck.h"
#include "UserModule.h"
#include <boost/filesystem.hpp>
#include "boost-utils.h"
namespace fs = boost::filesystem;

ModuleInstantiation::~ModuleInstantiation()
{
}

IfElseModuleInstantiation::~IfElseModuleInstantiation()
{
}

void ModuleInstantiation::print(std::ostream &stream, const std::string &indent, const bool inlined) const
{
	if (!inlined) stream << indent;
	stream << modname + "(";
	for (size_t i=0; i < this->arguments.size(); ++i) {
		const auto &arg = this->arguments[i];
		if (i > 0) stream << ", ";
		if (!arg->getName().empty()) stream << arg->getName() << " = ";
		stream << *arg->getExpr();
	}
	if (scope.numElements() == 0) {
		stream << ");\n";
	} else if (scope.numElements() == 1) {
		stream << ") ";
		scope.print(stream, indent, true);
	} else {
		stream << ") {\n";
		scope.print(stream, indent + "\t", false);
		stream << indent << "}\n";
	}
}

void IfElseModuleInstantiation::print(std::ostream &stream, const std::string &indent, const bool inlined) const
{
	ModuleInstantiation::print(stream, indent, inlined);
	if (else_scope) {
		auto num_elements = else_scope->numElements();
		if (num_elements == 0) {
			stream << indent << "else;";
		}
		else {
			stream << indent << "else ";
			if (num_elements == 1) {
				else_scope->print(stream, indent, true);
			}
			else {
				stream << "{\n";
				else_scope->print(stream, indent + "\t", false);
				stream << indent << "}\n";
			}
		}
	}
}

/**
 * This is separated because PRINTB uses quite a lot of stack space
 * and the method using it evaluate()
 * is called often when recursive modules are evaluated.
 * noinline is required, as we here specifically optimize for stack usage
 * during normal operating, not runtime during error handling.
*/
static void NOINLINE print_trace(const ModuleInstantiation *mod, const std::shared_ptr<const Context> context){
	LOG(message_group::Trace,mod->location(),context->documentRoot(),"called by '%1$s'",mod->name());
}

static void NOINLINE print_err(std::string name, const Location &loc,const std::shared_ptr<const Context> context){
	LOG(message_group::Error,loc,context->documentRoot(),"Recursion detected calling module '%1$s'",name);
}

AbstractNode *ModuleInstantiation::evaluate(const std::shared_ptr<const Context> context) const
{
	if (StackCheck::inst().check()) {
		print_err(name(),loc,context);
		throw RecursionException::create("module", name(), loc);
		return nullptr;
	}
	
	unsigned int recursion_depth = 0;
	const ModuleInstantiation* current_instantiation = this;
	std::vector<StaticModuleNameStack> module_name_stack;
	
	ContextHandle<Context> instantiation_context{Context::create<Context>(context)};
	const ModuleInstantiation* instantiation = this;
	AbstractNode* user_module_node = nullptr;
	while (true) {
		try {
			boost::optional<InstantiableModule> module = instantiation_context->lookup_module(instantiation->name(), instantiation->loc);
			if (!module) {
				return user_module_node;
			}
			
			const LocalScope* scope = nullptr;
			boost::optional<ContextHandle<Context>> new_context;
			const ModuleInstantiation* new_instantiation = nullptr;
			
			const UserModule* user_module = dynamic_cast<const UserModule*>(module->module);
			if (user_module && !instantiation->scope.hasChildren()) {
				module_name_stack.emplace_back(instantiation->name());
				
				ContextHandle<UserModuleContext> module_context{Context::create<UserModuleContext>(
					module->defining_context,
					user_module,
					instantiation->location(),
					Arguments(instantiation->arguments, *instantiation_context),
					Children(nullptr)
				)};
				
				scope = &user_module->body;
				new_context = std::move(module_context);
				new_instantiation = instantiation;
			}
			else if (!user_module_node) {
				return module->module->instantiate(module->defining_context, instantiation, *instantiation_context);
			}
			else if (const IfElseModuleInstantiation* ifelse = dynamic_cast<const IfElseModuleInstantiation*>(instantiation)) {
				Arguments arguments{instantiation->arguments, *instantiation_context};
				if (arguments.size() > 0 && arguments[0]->toBool()) {
					scope = &instantiation->scope;
				} else if (ifelse->getElseScope()) {
					scope = ifelse->getElseScope();
				} else {
					return user_module_node;
				}
			}
			else {
				AbstractNode *node = module->module->instantiate(module->defining_context, instantiation, *instantiation_context);
				if (node) {
					user_module_node->children.push_back(node);
				}
				return user_module_node;
			}
			
			if (!new_context) {
				new_context = Context::create<ScopeContext>(*instantiation_context, scope);
			}
			(*new_context)->apply_missing_config_variables(*(*instantiation_context).get());
			instantiation_context = std::move(*new_context);
			
			if (!user_module_node) {
				user_module_node = new GroupNode(instantiation, std::string("module ") + instantiation->name());
			}
			
			for (int i = 0; i < (int)scope->moduleInstantiations.size() - 1; i++) {
				AbstractNode* node = scope->instantiateModule(*instantiation_context, i);
				if (node) {
					user_module_node->children.push_back(node);
				}
			}
			
			if (scope->moduleInstantiations.size() == 0) {
				return user_module_node;
			} else {
				instantiation = scope->moduleInstantiations[scope->moduleInstantiations.size() - 1].get();
			}
			
			if (new_instantiation) {
				current_instantiation = new_instantiation;
				if (recursion_depth++ == 100000000) {
					LOG(message_group::Error,instantiation->location(),instantiation_context->documentRoot(),"Recursion detected calling module '%1$s'",current_instantiation->name());
					throw RecursionException::create("module", instantiation->name(), instantiation->location());
				}
			}
		} catch (EvaluationException &e) {
			if (e.traceDepth > 0) {
				print_trace(current_instantiation, context);
				e.traceDepth--;
			}
			throw;
		}
	}
}

LocalScope* IfElseModuleInstantiation::makeElseScope()
{
	this->else_scope = std::make_unique<LocalScope>();
	return this->else_scope.get();
}

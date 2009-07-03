
CONFIG += qt debug
TEMPLATE = app

DEFINES += "ENABLE_CGAL=1"
LIBS += -lCGAL -lmpfr

DEFINES += "ENABLE_OPENCSG=1"
LIBS += -lopencsg -lGLEW

LEXSOURCES += lexer.l
YACCSOURCES += parser.y

HEADERS += openscad.h
SOURCES += openscad.cc mainwin.cc glview.cc
SOURCES += value.cc expr.cc func.cc module.cc context.cc
SOURCES += csgterm.cc polyset.cc csgops.cc transform.cc
SOURCES += primitives.cc control.cc

QMAKE_CXXFLAGS += -O3 -march=pentium
// QMAKE_CXXFLAGS += -O3 -march=athlon64

QT += opengl


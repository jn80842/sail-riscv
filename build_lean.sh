#!/bin/bash

set -e
cmake -S . -B build -DCMAKE_BUILD_TYPE=RelWithDebInfo
jobs=$( (nproc || sysctl -n hw.ncpu || echo 2) 2>/dev/null)
cmake --build build/ -j${jobs} --target generated_lean_rv64d_lean

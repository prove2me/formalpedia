-- Prove2me | solution 1 for FamousTheorems.tower_law_field_degrees_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:33:03.720175+00:00
-- url     : https://prove2.me/submissions/b387c5ce-1df4-4fbb-8f06-ee2177017f49

import Mathlib

theorem solution (F K A : Type*) [Field F] [Field K] [Field A] [Algebra F K] [Algebra K A] [Algebra F A]
    [IsScalarTower F K A] : Module.finrank F K * Module.finrank K A = Module.finrank F A :=
  Module.finrank_mul_finrank F K A

-- Prove2me | solution 1 for FamousTheorems.trace_form_nondegenerate_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:04:42.164674+00:00
-- url     : https://prove2.me/submissions/e50c7716-ce9b-46da-8556-b5e69c9be2d2

import Mathlib

theorem solution (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    (Algebra.traceForm K L).Nondegenerate :=
  traceForm_nondegenerate K L

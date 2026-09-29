-- Prove2me | solution 1 for FamousTheorems.number_field_discriminant_norm_different_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:01:45.232987+00:00
-- url     : https://prove2.me/submissions/85bf785f-22c7-4909-bb0d-17510ff398ec

import Mathlib

theorem solution (K : Type*) [Field K] [NumberField K] :
    Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers K)) = (NumberField.discr K).natAbs :=
  NumberField.absNorm_differentIdeal K _

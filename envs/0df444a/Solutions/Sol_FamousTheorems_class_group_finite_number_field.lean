-- Prove2me | solution 1 for FamousTheorems.class_group_finite_number_field
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:21:06.912901+00:00
-- url     : https://prove2.me/submissions/d932f814-2228-493c-b86a-a5ef2b607344

import Mathlib

theorem solution (K : Type*) [Field K] [NumberField K] : Finite (ClassGroup (NumberField.RingOfIntegers K)) :=
  inferInstance

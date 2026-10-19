-- Prove2me | solution 1 for CompactnessConjecture.symmetricDet_zero_diagonal_sub_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/d85ba6b5-8d0e-4f1a-a98b-4d8ccd4602d4

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symmetricDet_zero_diagonal_sub

set_option autoImplicit true
open CompactnessConjecture
variable {K : Type*} [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {b b' : K} (h : b ≠ b') :
    symmetricDet (0 : K) (b - b') 0 ≠ 0 := by
  rw [symmetricDet_zero_diagonal_sub]
  exact neg_ne_zero.mpr (pow_ne_zero 2 (sub_ne_zero.mpr h))
end CompactnessConjecture

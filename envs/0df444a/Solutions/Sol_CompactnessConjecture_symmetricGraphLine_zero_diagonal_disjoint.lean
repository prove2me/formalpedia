-- Prove2me | solution 1 for CompactnessConjecture.symmetricGraphLine_zero_diagonal_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/455548dd-4bfa-40eb-b3c6-609dceab5a4e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symmetricDet_zero_diagonal_sub_ne_zero
import Theorems.Thm_CompactnessConjecture_symmetricGraphLines_disjoint_of_difference_det

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {b b' : K} (h : b ≠ b') :
    Disjoint (symmetricGraphLine K 0 b 0).1
      (symmetricGraphLine K 0 b' 0).1 := by
  apply symmetricGraphLines_disjoint_of_difference_det K
  simpa using symmetricDet_zero_diagonal_sub_ne_zero h
end CompactnessConjecture

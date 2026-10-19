-- Prove2me | solution 1 for CompactnessConjecture.symplecticLine_eq_invertible_symmetricGraphLine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/aeafdf47-d2a5-4cdf-b160-d586d7ea5069

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticLine_eq_symmetricGraphLine_of_disjoint_vertical
import Theorems.Thm_CompactnessConjecture_symmetricGraphLine_det_ne_zero_of_disjoint_horizontal

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (hhorizontal :
      Disjoint L.1 (symmetricGraphLine K 0 0 0).1) :
    ∃ a b c : K,
      L = symmetricGraphLine K a b c ∧
        symmetricDet a b c ≠ 0 := by
  obtain ⟨a, b, c, hL⟩ :=
    symplecticLine_eq_symmetricGraphLine_of_disjoint_vertical
      K L hvertical
  refine ⟨a, b, c, hL, ?_⟩
  apply symmetricGraphLine_det_ne_zero_of_disjoint_horizontal K a b c
  rw [← hL]
  exact hhorizontal
end CompactnessConjecture

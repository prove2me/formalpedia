-- Prove2me | solution 1 for CompactnessConjecture.symmetricGraphLine_odd_no_three_actual_centers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/3e155e0e-c62f-4260-a9eb-a730294a8614

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symmetricQuadratic_no_three_roots_of_det_ne_zero
import Theorems.Thm_CompactnessConjecture_symmetricGraphLine_coordinateCenter_common_point_iff

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (htwo : (2 : K) ≠ 0)
    {a b c x₀ y₀ x₁ y₁ x₂ y₂ : K}
    (hdet : symmetricDet a b c ≠ 0)
    (h01 : x₀ * y₁ - x₁ * y₀ ≠ 0)
    (h02 : x₀ * y₂ - x₂ * y₀ ≠ 0)
    (h12 : x₁ * y₂ - x₂ * y₁ ≠ 0)
    (hcenter₀ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₀ y₀
            (projectiveDirection_nonzero_left K h01)).1)
    (hcenter₁ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₁ y₁
            (projectiveDirection_nonzero_right K h01)).1)
    (hcenter₂ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₂ y₂
            (projectiveDirection_nonzero_right K h02)).1) :
    False := by
  apply symmetricQuadratic_no_three_roots_of_det_ne_zero
    htwo hdet h01 h02 h12
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_left K h01)).mp hcenter₀
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_right K h01)).mp hcenter₁
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_right K h02)).mp hcenter₂
end CompactnessConjecture

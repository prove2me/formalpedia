-- Prove2me | solution 1 for CompactnessConjecture.symmetricQuadraticEvaluationMatrix_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/6b24c335-74c1-4bd7-a6e5-1904b1e935fa

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
variable {K : Type*} [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (x₀ y₀ x₁ y₁ x₂ y₂ : K) :
    (symmetricQuadraticEvaluationMatrix x₀ y₀ x₁ y₁ x₂ y₂).det =
      (2 : K) * (x₀ * y₁ - x₁ * y₀) *
        (x₀ * y₂ - x₂ * y₀) * (x₁ * y₂ - x₂ * y₁) := by
  rw [Matrix.det_fin_three]
  simp [symmetricQuadraticEvaluationMatrix]
  ring
end CompactnessConjecture

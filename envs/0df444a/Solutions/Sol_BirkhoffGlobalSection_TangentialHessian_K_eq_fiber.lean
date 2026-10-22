-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.K_eq_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T22:45:22.211301+00:00
-- url     : https://prove2.me/submissions/96199c3f-8a8e-46ea-b654-5884f0f6b0ce

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian_Fiber
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

namespace BirkhoffGlobalSection.TangentialHessian.ReductionDAux

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian

/-- The `w`-coordinates of the gradient: `u = w + b(z)`. -/
theorem kGradR_u (μ c r : ℝ) (s : Phase) :
    kGradR μ c r s 2 = s 2 - (2 * zNormSq s + μ) * s 1 ∧
      kGradR μ c r s 3 = s 3 + (2 * zNormSq s - μ) * s 0 := by
  constructor <;> simp [kGradR, dP, dZ, dD, zNormSq] <;> ring

end BirkhoffGlobalSection.TangentialHessian.ReductionDAux

open Matrix in
open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian BirkhoffGlobalSection.TangentialHessian.ReductionDAux in
theorem solution (μ c r : ℝ) (s : Phase) :
    pP μ c s - μ * (zNormSq s / r) =
      (kGradR μ c r s 2 ^ 2 + kGradR μ c r s 3 ^ 2) / 2 - fibF μ c r s / 2 := by
  obtain ⟨h2, h3⟩ := kGradR_u μ c r s
  rw [h2, h3]
  simp only [pP, fibF, wNormSq, zNormSq]
  ring

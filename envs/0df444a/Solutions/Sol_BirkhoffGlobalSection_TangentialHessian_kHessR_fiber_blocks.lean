-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.kHessR_fiber_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T22:45:23.506887+00:00
-- url     : https://prove2.me/submissions/bf03a660-f9c2-45a8-9e22-4dfcd471f6bb

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian_Fiber
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

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
    kHessR μ c r s 0 0 - kHessR μ c r s 0 2 ^ 2 - kHessR μ c r s 0 3 ^ 2
        = fibL00 μ c r s + kGradR μ c r s 2 * (-4 * s 1) + kGradR μ c r s 3 * (12 * s 0) ∧
    kHessR μ c r s 1 1 - kHessR μ c r s 1 2 ^ 2 - kHessR μ c r s 1 3 ^ 2
        = fibL11 μ c r s + kGradR μ c r s 2 * (-12 * s 1) + kGradR μ c r s 3 * (4 * s 0) ∧
    kHessR μ c r s 0 1 - kHessR μ c r s 0 2 * kHessR μ c r s 1 2 - kHessR μ c r s 0 3 * kHessR μ c r s 1 3
        = fibL01 μ r s + kGradR μ c r s 2 * (-4 * s 0) + kGradR μ c r s 3 * (4 * s 1) ∧
    kGradR μ c r s 0 - kHessR μ c r s 0 2 * kGradR μ c r s 2 - kHessR μ c r s 0 3 * kGradR μ c r s 3
        = fibV0 μ c r s ∧
    kGradR μ c r s 1 - kHessR μ c r s 1 2 * kGradR μ c r s 2 - kHessR μ c r s 1 3 * kGradR μ c r s 3
        = fibV1 μ c r s := by
  obtain ⟨h2, h3⟩ := kGradR_u μ c r s
  rw [h2, h3]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [kHessR, kGradR, fibL00, fibL01, fibL11, fibV0, fibV1, kBr, hP, dP, hZ, hD, dZ, dD,
      zNormSq] <;> ring

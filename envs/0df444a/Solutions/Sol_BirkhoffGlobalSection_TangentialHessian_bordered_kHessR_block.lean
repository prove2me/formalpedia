-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.bordered_kHessR_block
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T22:45:17.589844+00:00
-- url     : https://prove2.me/submissions/3e942de9-cbb5-49e4-adb0-6403be34fafa

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Theorems.Thm_bordered_unit_block
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_kHessR_transpose
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

/-- (b) The `w`-block of `kHessR` is the identity. -/
theorem kHessR_w_block (μ c r : ℝ) (s : Phase) :
    kHessR μ c r s 2 2 = 1 ∧ kHessR μ c r s 3 3 = 1 ∧ kHessR μ c r s 2 3 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [kHessR, hP, hZ, hD, dZ, dD]

end BirkhoffGlobalSection.TangentialHessian.ReductionDAux

open Matrix in
open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian BirkhoffGlobalSection.TangentialHessian.ReductionDAux in
theorem solution (μ c r : ℝ) (s : Phase) :
    kGradR μ c r s ⬝ᵥ (kHessR μ c r s).adjugate.mulVec (kGradR μ c r s) =
      (kGradR μ c r s 2 ^ 2 + kGradR μ c r s 3 ^ 2) *
          ((kHessR μ c r s 0 0 - kHessR μ c r s 0 2 ^ 2 - kHessR μ c r s 0 3 ^ 2) *
              (kHessR μ c r s 1 1 - kHessR μ c r s 1 2 ^ 2 - kHessR μ c r s 1 3 ^ 2)
            - (kHessR μ c r s 0 1 - kHessR μ c r s 0 2 * kHessR μ c r s 1 2
                - kHessR μ c r s 0 3 * kHessR μ c r s 1 3) ^ 2) +
        ((kHessR μ c r s 1 1 - kHessR μ c r s 1 2 ^ 2 - kHessR μ c r s 1 3 ^ 2) *
            (kGradR μ c r s 0 - kHessR μ c r s 0 2 * kGradR μ c r s 2
              - kHessR μ c r s 0 3 * kGradR μ c r s 3) ^ 2
          - 2 * (kHessR μ c r s 0 1 - kHessR μ c r s 0 2 * kHessR μ c r s 1 2
                - kHessR μ c r s 0 3 * kHessR μ c r s 1 3) *
              (kGradR μ c r s 0 - kHessR μ c r s 0 2 * kGradR μ c r s 2
                - kHessR μ c r s 0 3 * kGradR μ c r s 3) *
              (kGradR μ c r s 1 - kHessR μ c r s 1 2 * kGradR μ c r s 2
                - kHessR μ c r s 1 3 * kGradR μ c r s 3)
          + (kHessR μ c r s 0 0 - kHessR μ c r s 0 2 ^ 2 - kHessR μ c r s 0 3 ^ 2) *
            (kGradR μ c r s 1 - kHessR μ c r s 1 2 * kGradR μ c r s 2
              - kHessR μ c r s 1 3 * kGradR μ c r s 3) ^ 2) := by
  obtain ⟨h22, h33, h23⟩ := kHessR_w_block μ c r s
  exact bordered_unit_block _ _ (kHessR_transpose μ c r s) h22 h33 h23

-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.dup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:00:08.473637+00:00
-- url     : https://prove2.me/submissions/e752ae39-a58f-43ba-9964-9435defea11c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_psi_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.KNorm
open Formalism.ELL (InFormalGroupPoints)
open Formalism.L2.Th1.E (px py IntCurve)
open WeierstrassCurve.Affine (Point)
variable {K : Type} [Field K] {W : WeierstrassCurve K} {x y : K}
variable [DecidableEq K]
namespace Formalism.L2.Th1.B.KNorm
theorem _root_.solution (h : W.toAffine.Equation x y) (hy : y ≠ W.toAffine.negY x y) :
    W.toAffine.addX x x (W.toAffine.slope x x y y)
        * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
      = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
  have hden : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.2 hy
  have hdd : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
    rw [WeierstrassCurve.Affine.negY]
    ring
  have hl : W.toAffine.slope x x y y * (2 * y + W.a₁ * x + W.a₃)
      = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, ← hdd, div_mul_cancel₀ _ hden]
  rw [← psi_eq h, WeierstrassCurve.Affine.addX]
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination (W.toAffine.slope x x y y * (2 * y + W.a₁ * x + W.a₃)
      + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) + W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * hl
    + (-(W.a₁ ^ 2 + 4 * W.a₂ + 8 * x)) * h
end Formalism.L2.Th1.B.KNorm

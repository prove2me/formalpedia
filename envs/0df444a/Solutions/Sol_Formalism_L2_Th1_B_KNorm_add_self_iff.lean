-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.add_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:01:37.473383+00:00
-- url     : https://prove2.me/submissions/264a8a16-dfa7-4fb5-99f6-c36aae1925f4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_negY_iff

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
theorem _root_.solution (h : W.toAffine.Nonsingular x y) :
    (Point.some x y h + Point.some x y h = 0) ↔ 2 * y + W.a₁ * x + W.a₃ = 0 := by
  rw [add_eq_zero_iff_eq_neg, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
  simp only [true_and]
  exact negY_iff
end Formalism.L2.Th1.B.KNorm

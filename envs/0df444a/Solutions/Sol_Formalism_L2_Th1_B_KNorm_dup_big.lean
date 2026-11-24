-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.dup_big
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:14.283797+00:00
-- url     : https://prove2.me/submissions/a1604868-8988-459d-919e-bf9cd2b3e819

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_b_int
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_dup_core
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_negY_iff
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_dup
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_add_self_iff
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_px_add_self

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
variable {K : Type} [NormedField K] [IsUltrametricDist K] [DecidableEq K]
  {W : WeierstrassCurve K}
namespace Formalism.L2.Th1.B.KNorm
theorem _root_.solution (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (P : W.toAffine.Point)
    (hx : 4 ≤ ‖px W P‖) (hP : P + P ≠ 0) : 4 < ‖px W (P + P)‖ := by
  obtain ⟨h1, h2a, h3, h4, h6, -⟩ := hW
  obtain ⟨hb2, hb4, hb6, hb8⟩ := b_int W h1 h2a h3 h4 h6
  cases P with
  | zero =>
    change 4 ≤ ‖(0 : K)‖ at hx
    rw [norm_zero] at hx
    norm_num at hx
  | some x y h =>
    have hy : y ≠ W.toAffine.negY x y := fun e => hP ((add_self_iff h).2 (negY_iff.1 e))
    rw [px_add_self h hy]
    exact dup_core h2 hb2 hb4 hb6 hb8 hx (dup h.1 hy)
end Formalism.L2.Th1.B.KNorm

-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.two_tors_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:15.671818+00:00
-- url     : https://prove2.me/submissions/d9f83a0b-ff61-4828-95be-90945d36683b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_b_int
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_psi_zero_le
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_psi_eq
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_add_self_iff

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
    (hP : P + P = 0) : ‖px W P‖ ≤ 4 := by
  obtain ⟨h1, h2a, h3, h4, h6, -⟩ := hW
  obtain ⟨hb2, hb4, hb6, -⟩ := b_int W h1 h2a h3 h4 h6
  cases P with
  | zero =>
    change ‖(0 : K)‖ ≤ 4
    rw [norm_zero]
    norm_num
  | some x y h =>
    have hd := (add_self_iff h).1 hP
    have h0 := psi_eq h.1
    rw [hd] at h0
    exact psi_zero_le (x := x) h2 hb2 hb4 hb6 (by rw [← h0]; ring)
end Formalism.L2.Th1.B.KNorm

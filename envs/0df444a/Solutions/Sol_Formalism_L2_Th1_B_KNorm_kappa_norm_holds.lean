-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.kappa_norm_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:14.938501+00:00
-- url     : https://prove2.me/submissions/5f9fd894-6086-48e6-a3a7-eac6571abc31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_nadd_lt
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_ndom
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_n3
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_b_int

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
namespace Formalism.L2.Th1.B.KNorm
theorem _root_.solution : KapNorm := by
  intro K _ _ _ W hM h2 x
  obtain ⟨h1, h2a, h3, h4, h6⟩ := hM
  obtain ⟨hb2, hb4, -, -⟩ := b_int W h1 h2a h3 h4 h6
  have e : 3 * (x + W.b₂ / 12) ^ 2 - Formalism.L2.Th1.A.g₂ W / 4
      = 3 * x ^ 2 + 2⁻¹ * W.b₂ * x + 2⁻¹ * W.b₄ := by
    simp only [Formalism.L2.Th1.A.g₂, WeierstrassCurve.c₄]
    ring
  have ni : ‖(2 : K)⁻¹‖ = 2 := by rw [norm_inv, h2, inv_inv]
  have t1 : ‖3 * x ^ 2‖ = ‖x‖ ^ 2 := by rw [norm_mul, n3 h2, one_mul, norm_pow]
  have t2 : ‖2⁻¹ * W.b₂ * x‖ ≤ 2 * ‖x‖ := by
    rw [norm_mul, norm_mul, ni]
    nlinarith [mul_le_mul_of_nonneg_right hb2 (norm_nonneg x), norm_nonneg W.b₂]
  have t3 : ‖2⁻¹ * W.b₄‖ ≤ 2 := by
    rw [norm_mul, ni]
    linarith
  rw [e]
  constructor
  · intro hx
    have hr : ‖2⁻¹ * W.b₂ * x + 2⁻¹ * W.b₄‖ < ‖3 * x ^ 2‖ := by
      rw [t1, hx]
      exact nadd_lt (t2.trans_lt (by rw [hx]; norm_num)) (t3.trans_lt (by norm_num))
    rw [add_assoc, ndom hr, t1, hx]
    norm_num
  · intro hx
    have r0 := norm_nonneg x
    exact nadd_lt (nadd_lt (by rw [t1]; nlinarith) (t2.trans_lt (by linarith))) (t3.trans_lt (by norm_num))
end Formalism.L2.Th1.B.KNorm

-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.two_torsion_kernel_norm_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:16.957913+00:00
-- url     : https://prove2.me/submissions/54501cee-b67a-422c-afe9-a096b89ecdef

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_ndom
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_n4
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_two_ne
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_b_int
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_psi_zero_eq
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_psi_zero_unique
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
theorem _root_.solution (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (ha : ‖W.a₁‖ = 1)
    (P Q : W.toAffine.Point) (hP0 : P ≠ 0) (hP : P + P = 0) (hPE : InFormalGroupPoints P) :
    ‖px W P‖ = 4 ∧ (Q ≠ 0 → Q + Q = 0 → InFormalGroupPoints Q → P = Q) := by
  obtain ⟨h1, h2a, h3, h4, h6, -⟩ := hW
  obtain ⟨-, hb4, hb6, -⟩ := b_int W h1 h2a h3 h4 h6
  have hb2 : ‖W.b₂‖ = 1 := by
    simp only [WeierstrassCurve.b₂]
    rw [ndom (by rw [norm_pow, ha, one_pow, norm_mul, n4 h2]; nlinarith [norm_nonneg W.a₂]),
      norm_pow, ha, one_pow]
  cases P with
  | zero => exact (hP0 rfl).elim
  | some x y h =>
    have hd := (add_self_iff h).1 hP
    have h0 : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
      have e := psi_eq h.1
      rw [hd] at e
      rw [← e]
      ring
    have hx4 : ‖x‖ = 4 := psi_zero_eq (x := x) h2 hb2 hb4 hb6 hPE h0
    refine ⟨hx4, fun hQ0 hQ hQE => ?_⟩
    cases Q with
    | zero => exact (hQ0 rfl).elim
    | some x' y' h' =>
      have hd' := (add_self_iff h').1 hQ
      have h0' : 4 * x' ^ 3 + W.b₂ * x' ^ 2 + 2 * W.b₄ * x' + W.b₆ = 0 := by
        have e := psi_eq h'.1
        rw [hd'] at e
        rw [← e]
        ring
      have hx4' : ‖x'‖ = 4 := psi_zero_eq (x := x') h2 hb2 hb4 hb6 hQE h0'
      have hxx := psi_zero_unique h2 hb2.le hb4 hb6 hx4 hx4' h0 h0'
      subst hxx
      have hyy : y = y' := by
        have e2 : (2 : K) * y = 2 * y' := by linear_combination hd - hd'
        exact mul_left_cancel₀ (two_ne h2) e2
      subst hyy
      rfl
end Formalism.L2.Th1.B.KNorm

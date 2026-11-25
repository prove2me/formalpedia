-- Prove2me | solution 1 for Formalism.L2.Th1.A.flow_unique_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:00.939504+00:00
-- url     : https://prove2.me/submissions/945174d8-f332-4259-b6c1-63cc353611c1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_NormLeOneOfMonicTwo
import Theorems.Thm_Formalism_ELL_EulerSeries_Agree_mul_right
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_eq_zero_of_forall_X_pow_dvd
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_Nn_X_pow_succ_dvd_of_derivative
import Theorems.Thm_Formalism_L2_Th1_A_Nn_eq_zero_of_forall_X_pow_dvd
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Q2
namespace Formalism.L2.Th1.A
theorem _root_.solution : FlowUniqueZ.{u} := by
  intro K _ _ W x y x' y' hF hF' hx0 hy0
  obtain ⟨-, hx, hy⟩ := hF
  obtain ⟨-, hx', hy'⟩ := hF'
  have hR : ∀ (n : ℕ) (r : K), n ≠ 0 → (n : K) * r = 0 → r = 0 := fun n r hn h =>
    (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 hn)
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄] at hx hy hx' hy'
  have dx : derivative K (x - x') = 2 * (y - y') + C W.a₁ * (x - x') := by
    rw [map_sub, hx, hx']; ring
  have dy : derivative K (y - y')
      = (x - x') * (3 * (x + x') + 2 * C W.a₂) - C W.a₁ * (y - y') := by
    rw [map_sub, hy, hy']; ring
  have cx : constantCoeff (x - x') = 0 := by rw [map_sub, hx0, sub_self]
  have cy : constantCoeff (y - y') = 0 := by rw [map_sub, hy0, sub_self]
  have key : ∀ n : ℕ, X ^ n ∣ x - x' ∧ X ^ n ∣ y - y' := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨ix, iy⟩ := ih
      refine ⟨Nn.X_pow_succ_dvd_of_derivative hR cx ?_, Nn.X_pow_succ_dvd_of_derivative hR cy ?_⟩
      · rw [dx]
        exact dvd_add (Dvd.dvd.mul_left iy _) (Dvd.dvd.mul_left ix _)
      · rw [dy]
        exact dvd_sub (Dvd.dvd.mul_right ix _) (Dvd.dvd.mul_left iy _)
  exact ⟨sub_eq_zero.1 (Nn.eq_zero_of_forall_X_pow_dvd fun n => (key n).1),
    sub_eq_zero.1 (Nn.eq_zero_of_forall_X_pow_dvd fun n => (key n).2)⟩
end Formalism.L2.Th1.A

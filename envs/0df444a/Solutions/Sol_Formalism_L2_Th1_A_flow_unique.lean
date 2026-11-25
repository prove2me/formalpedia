-- Prove2me | solution 1 for Formalism.L2.Th1.A.flow_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:10.407819+00:00
-- url     : https://prove2.me/submissions/92a0c563-6e52-4496-a360-4da658eb797d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_XPowSuccDvdOfDerivative
import Theorems.Thm_Formalism_L2_Th1_A_Nn_X_pow_succ_dvd_of_derivative
import Theorems.Thm_Formalism_L2_Th1_A_Nn_eq_zero_of_forall_X_pow_dvd
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_eq_zero_of_forall_X_pow_dvd
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_invariant_differential_units
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
open Nn
namespace Formalism.L2.Th1.A
theorem _root_.solution : FlowUnique.{u} := by
  rintro R _ W x y x' y' hR ⟨-, hx, hy⟩ ⟨-, hx', hy'⟩ h0x h0y
  have hfo : fw W * om W = 1 := (invariant_differential_units R W).2.1
  have eD : ∀ g : R⟦X⟧, derivative R g = om W * D W g := fun g => by
    simp only [D, Derivation.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_comm (om W), hfo, one_mul]
  have key : ∀ n : ℕ, X ^ n ∣ x - x' ∧ X ^ n ∣ y - y' := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
      constructor
      · apply X_pow_succ_dvd_of_derivative hR (by rw [map_sub, h0x, sub_self])
        refine ⟨om W * (2 * b + (curveS W).a₁ * a), ?_⟩
        rw [map_sub, eD x, eD x', hx, hx']
        linear_combination (2 * om W) * hb + ((curveS W).a₁ * om W) * ha
      · apply X_pow_succ_dvd_of_derivative hR (by rw [map_sub, h0y, sub_self])
        refine ⟨om W * (3 * (x + x') * a + 2 * (curveS W).a₂ * a - (curveS W).a₁ * b), ?_⟩
        rw [map_sub, eD y, eD y', hy, hy']
        linear_combination (om W * (3 * (x + x') + 2 * (curveS W).a₂)) * ha
          - ((curveS W).a₁ * om W) * hb
  constructor
  · exact sub_eq_zero.mp (eq_zero_of_forall_X_pow_dvd fun n => (key n).1)
  · exact sub_eq_zero.mp (eq_zero_of_forall_X_pow_dvd fun n => (key n).2)
end Formalism.L2.Th1.A

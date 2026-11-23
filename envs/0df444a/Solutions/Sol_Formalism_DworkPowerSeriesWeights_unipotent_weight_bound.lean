-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.unipotent_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:16:32.075826+00:00
-- url     : https://prove2.me/submissions/4203d416-979e-4a80-8b7a-ef69d0d3bfb9

import Definitions.Def_Formalism_GaussJetBounds_StatementO
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LemmaRA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbits
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitsLogLoss
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_nonneg
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_single
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_generalized_log_weight
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_radical_weight_monotone
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_substitution_weight_bound
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : UWt.{u, v, w} := by
  classical
  intro K _ _ _ l hl hpi τ _ _ p g hg0 hg U hU ι _ M hM1 sig hsig
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have h1 : ‖(l : K)‖ ≤ 1 := hpi.le
  have hrho : 0 ≤ rho l := by
    unfold rho
    apply div_nonneg zero_le_one
    nlinarith
  have hr : ∀ i, (fun _ : ι => rho l) i ≤ (fun i => rho l + sig i) i := fun i => by
    simp only
    linarith [hsig i]
  have hlin0 : ∀ x, MvPowerSeries.constantCoeff
      (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i : MvPowerSeries ι K) = 0 := by
    intro x
    simp
  have hU0 : WtGe ‖(l : K)‖ (fun _ : τ => rho l) 0 U := by
    intro n
    rw [monoWtGe_iff]
    refine le_trans (hU n) (Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 ?_)
    linarith [asmR_dot_nonneg n (r := fun _ : τ => rho l) fun _ => hrho]
  have hgw := generalized_log_weight K l hl hpi τ p g hg0 hg
  have hgU : WtGe ‖(l : K)‖ (fun _ : τ => rho l) 0 (MvPowerSeries.subst g U) :=
    substitution_weight_bound K ‖(l : K)‖ h0 hpi τ τ g (fun _ => rho l) (fun _ => rho l) 0 U hg0 hgw hU0
  have hlinw : ∀ x, WtGe ‖(l : K)‖ (fun _ : ι => rho l) (rho l)
      (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i : MvPowerSeries ι K) := by
    intro x n
    rw [monoWtGe_iff]
    simp only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _)
      fun i _ => ?_
    split_ifs with h
    · subst h
      rw [mul_one, asmR_dot_single]
      simpa using hM1 x i
    · simpa using Real.rpow_nonneg h0.le _
  have hY : WtGe ‖(l : K)‖ (fun _ : ι => rho l) 0
      (MvPowerSeries.subst (fun x => (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i :
        MvPowerSeries ι K)) (MvPowerSeries.subst g U)) :=
    substitution_weight_bound K ‖(l : K)‖ h0 hpi τ ι _ (fun _ => rho l) (fun _ => rho l) 0 _
      hlin0 hlinw hgU
  exact (radical_weight_monotone K ‖(l : K)‖ h0 hpi ι (fun _ => rho l) (fun i => rho l + sig i) 0 hr).1 _ hY
end Formalism.DworkPowerSeriesWeights

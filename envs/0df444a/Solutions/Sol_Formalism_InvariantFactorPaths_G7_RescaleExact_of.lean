-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.RescaleExact_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:53:26.542295+00:00
-- url     : https://prove2.me/submissions/8162db04-fdc1-4c1f-a811-04a7c6c5ef88

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_weight_ge_g_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_constant_coeff_g_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_subst_g_series_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_constant_coeff_hh_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_norm_unif
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_const
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_substitution_weight_bound
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero


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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low WtGe MonoWtGe dot dot_const substitution_weight_bound)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hT : ValTable) (hE : ExpIntegral) : RescaleExact := by
  intro K E _ _ _ _ p c c' ϖ hp hn hϖ hc hc'
  classical
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have hlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  let a : E → Fin 2 → MvPowerSeries (Bool × E) K := fun e z => MvPowerSeries.C ϖ *
      (MvPowerSeries.X (if z = 0 then (false, e) else (true, e)) : MvPowerSeries (Bool × E) K)
  have ha0 : ∀ e z, MvPowerSeries.constantCoeff (a e z) = 0 := fun e z => by simp [a]
  have hs : ∀ e, MvPowerSeries.HasSubst (a e) := fun e =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero (ha0 e)
  have hG : Gtot (E := E) p c c' ϖ =
      MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hh1 (E := E) p c c' +
        ∑ e : E, MvPowerSeries.subst (a e) (G1 p c c') := by
    unfold Gtot hh1
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine (subst_g_series_eq p c c' (hs e)).trans ?_
    have e1 : (MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) : MvPowerSeries (Bool × E) K) =
        MvPowerSeries.C ((p : K)⁻¹) * MvPowerSeries.C ϖ ^ (p + 1) := by
      rw [← map_pow, ← map_mul, div_eq_inv_mul]
    rw [e1]
    simp only [a, if_true, Fin.isValue, one_ne_zero, if_false]
    ring
  have hR0 : MvPowerSeries.constantCoeff (∑ e : E, MvPowerSeries.subst (a e) (G1 p c c')) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun e _ => (low_one_iff _).1
      (low_subst_of_low (ha0 e) ((low_one_iff _).2 (constant_coeff_g_one hp.ne_zero c c')))
  have hwa : ∀ e z, WtGe ((p : ℝ)⁻¹) (fun _ : Bool × E => (0 : ℝ)) (1 / ((p : ℝ) ^ 2 - 1))
      (a e z) := by
    intro e z m
    unfold MonoWtGe
    rw [dot_const, mul_zero, sub_zero, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    split_ifs <;>
      first
        | rw [mul_one, norm_unif hp hn hϖ]
        | (rw [mul_zero, norm_zero]; positivity)
  have hRn : ∀ n, ‖MvPowerSeries.coeff n (∑ e : E, MvPowerSeries.subst (a e) (G1 p c c'))‖ ≤
      (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
    intro n
    rw [map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun e _ => ?_
    have h := substitution_weight_bound K ((p : ℝ)⁻¹) hpos hlt (Fin 2) (Bool × E) (a e)
      (fun _ => 1 / ((p : ℝ) ^ 2 - 1)) (fun _ => 0) (1 / ((p : ℝ) - 1)) (G1 p c c') (ha0 e)
      (hwa e) (weight_ge_g_one hT hp hn hc hc') n
    unfold MonoWtGe at h
    rw [dot_const, mul_zero, sub_zero, Real.inv_rpow (by positivity), ← Real.rpow_neg
      (by positivity)] at h
    exact h
  refine ⟨mvExp (-(∑ e : E, MvPowerSeries.subst (a e) (G1 p c c'))),
    hE K _ p hp hn _ (by rw [map_neg, hR0, neg_zero])
      (fun n => by rw [map_neg, norm_neg]; exact hRn n), ?_⟩
  rw [hG, neg_add, mvExp_add (by rw [map_neg, map_mul, constant_coeff_hh_zero hp.ne_zero, mul_zero,
    neg_zero]) (by rw [map_neg, hR0, neg_zero])]
end Formalism.InvariantFactorPaths.G7

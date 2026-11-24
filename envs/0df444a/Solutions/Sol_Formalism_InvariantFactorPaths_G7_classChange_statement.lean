-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.classChange_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:46:37.457821+00:00
-- url     : https://prove2.me/submissions/bfae08d9-bb64-4029-b374-69d5bb1eabfc

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_low_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_inClass_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_low_chU
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_integral_chU
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_sum_triangle
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_term_change
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
theorem _root_.solution : ClassChange := by
  intro K ι _ _ pp hpp _ hh Y F h0 hY0 hY hF
  have h0' : MvPowerSeries.constantCoeff (hh + MvPowerSeries.C pp * Y) = 0 := by
    rw [map_add, map_mul, h0, hY0, mul_zero, add_zero]
  rw [inClass_iff h0] at hF
  rw [inClass_iff h0']
  obtain ⟨U, hU, h⟩ := hF
  refine ⟨chU Y U, integral_chU hY hU, fun M => ?_⟩
  have e : clSum pp hh U M = ∑ b ∈ range M, MvPowerSeries.C ((pp ^ b)⁻¹) *
      ((hh + MvPowerSeries.C pp * Y) ^ b * ∑ a ∈ range (M - b), chT Y U b a) := by
    unfold clSum
    rw [Finset.sum_congr rfl fun i _ => term_change hpp hh Y U i]
    rw [sum_triangle (fun b a => MvPowerSeries.C ((pp ^ b)⁻¹) *
        ((hh + MvPowerSeries.C pp * Y) ^ b * chT Y U b a)) M]
    exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum, Finset.mul_sum]
  have e2 : F - clSum pp (hh + MvPowerSeries.C pp * Y) (chU Y U) M =
      (F - clSum pp hh U M) + ∑ b ∈ range M, MvPowerSeries.C ((pp ^ b)⁻¹) *
        ((hh + MvPowerSeries.C pp * Y) ^ b * (∑ a ∈ range (M - b), chT Y U b a - chU Y U b)) := by
    rw [e]
    unfold clSum
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [e2]
  refine low_add (h M) (low_sum _ _ _ fun b hb => ?_)
  have hb' : b < M := mem_range.1 hb
  have := low_mul (low_zero (MvPowerSeries.C ((pp ^ b)⁻¹) : MvPowerSeries ι K))
    (low_mul (low_pow ((low_one_iff _).2 h0') b) (low_chU hY0 U b (M - b)))
  exact low_mono (by omega) this
end Formalism.InvariantFactorPaths.G7

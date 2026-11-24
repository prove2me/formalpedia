-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.weight_ge_g_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:46:32.972696+00:00
-- url     : https://prove2.me/submissions/c0ffa17a-8407-43dc-aa5f-10d012ccca35

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_wt_AA
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
theorem _root_.solution (hT : ValTable) {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ}
    (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) {c c' : K} (hc : ‖c‖ ≤ 1) (hc' : ‖c'‖ ≤ 1) :
    WtGe ((p : ℝ)⁻¹) (fun _ : Fin 2 => 1 / ((p : ℝ) ^ 2 - 1)) (1 / ((p : ℝ) - 1))
      (G1 p c c') := by
  intro d
  unfold MonoWtGe
  rw [dot_const, G1, map_sub, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (wt_AA hT hp hn (by decide) d)
  · rw [norm_neg, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc').trans (wt_AA hT hp hn (by decide) d)
end Formalism.InvariantFactorPaths.G7

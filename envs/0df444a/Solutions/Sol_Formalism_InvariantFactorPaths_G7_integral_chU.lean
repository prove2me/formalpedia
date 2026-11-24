-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.integral_chU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:25.139088+00:00
-- url     : https://prove2.me/submissions/9abc399a-4343-497b-affe-1b9669707c1d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_const
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_substitution_weight_bound
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
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
theorem _root_.solution {K ι : Type} [NormedField K] [IsUltrametricDist K] {Y : MvPowerSeries ι K}
    (hY : Integral Y) {U : ℕ → MvPowerSeries ι K} (hU : ∀ i, Integral (U i)) (b : ℕ) :
    Integral (chU Y U b) := by
  intro n
  change ‖∑ a ∈ range (n.degree + 1), MvPowerSeries.coeff n (chT Y U b a)‖ ≤ 1
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun a _ => ?_
  have hY' : Integral (-Y) := fun m => by rw [map_neg, norm_neg]; exact hY m
  rw [chT, MvPowerSeries.coeff_C_mul, norm_mul]
  exact mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one K _) (norm_nonneg _)
    (Formalism.FG.IntegralSubstitution.integral_mul (Formalism.FG.IntegralSubstitution.integral_pow hY' a) (hU _) n)
end Formalism.InvariantFactorPaths.G7

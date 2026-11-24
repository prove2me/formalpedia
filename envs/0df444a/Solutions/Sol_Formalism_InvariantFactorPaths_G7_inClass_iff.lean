-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.inClass_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:11.316508+00:00
-- url     : https://prove2.me/submissions/cd961da4-9b08-44c4-b2aa-2c35863b91be

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_low_pow_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_clSum
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
theorem _root_.solution {K ι : Type} [NormedField K] {pp : K} {hh : MvPowerSeries ι K}
    (h0 : MvPowerSeries.constantCoeff hh = 0) (F : MvPowerSeries ι K) :
    InClass pp hh F ↔ ∃ U : ℕ → MvPowerSeries ι K, (∀ i, Integral (U i)) ∧
      ∀ M, Low M (F - clSum pp hh U M) := by
  constructor
  · rintro ⟨U, hU, h⟩
    refine ⟨U, hU, fun M d hd => ?_⟩
    rw [map_sub, h d, coeff_clSum, sub_eq_zero]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun i _ hi => ?_
    rw [low_pow_mul h0 i (U i) d (by simp only [mem_range] at hi; omega), mul_zero]
  · rintro ⟨U, hU, h⟩
    refine ⟨U, hU, fun n => ?_⟩
    have := h (n.degree + 1) n (by omega)
    rwa [map_sub, coeff_clSum, sub_eq_zero] at this
end Formalism.InvariantFactorPaths.G7

-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.term_change
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:43.006323+00:00
-- url     : https://prove2.me/submissions/fdd89785-1b81-404e-be4d-2da5b8562332

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
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
theorem _root_.solution {K ι : Type} [Field K] {pp : K} (hpp : pp ≠ 0) (hh Y : MvPowerSeries ι K)
    (U : ℕ → MvPowerSeries ι K) (i : ℕ) :
    MvPowerSeries.C ((pp ^ i)⁻¹) * (hh ^ i * U i) =
      ∑ b ∈ range (i + 1), MvPowerSeries.C ((pp ^ b)⁻¹) *
        ((hh + MvPowerSeries.C pp * Y) ^ b * chT Y U b (i - b)) := by
  have e : hh = (hh + MvPowerSeries.C pp * Y) + MvPowerSeries.C pp * (-Y) := by ring
  conv_lhs => rw [e, add_pow, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨a, rfl⟩ : ∃ a, i = b + a := ⟨i - b, by simp only [mem_range] at hb; omega⟩
  have key : (MvPowerSeries.C ((pp ^ (b + a))⁻¹) : MvPowerSeries ι K) * MvPowerSeries.C pp ^ a =
      MvPowerSeries.C ((pp ^ b)⁻¹) := by
    rw [← map_pow, ← map_mul]
    congr 1
    field_simp
    ring
  rw [Nat.add_sub_cancel_left, chT, mul_pow, map_natCast, ← key]
  ring
end Formalism.InvariantFactorPaths.G7

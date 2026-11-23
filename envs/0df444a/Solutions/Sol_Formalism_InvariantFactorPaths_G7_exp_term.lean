-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.exp_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:38.593343+00:00
-- url     : https://prove2.me/submissions/1b12c798-4fc9-4fe8-bbfb-8b07a6b6f737

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
theorem _root_.solution {K ι : Type} [Field K] [CharZero K] (a b : MvPowerSeries ι K) (i : ℕ) :
    MvPowerSeries.C ((i.factorial : K)⁻¹) * (a + b) ^ i =
      ∑ k ∈ range (i + 1), (MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) *
        (MvPowerSeries.C (((i - k).factorial : K)⁻¹) * b ^ (i - k)) := by
  rw [add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨l, rfl⟩ : ∃ l, i = k + l := ⟨i - k, by simp only [mem_range] at hk; omega⟩
  have key : (MvPowerSeries.C (((k + l).factorial : K)⁻¹) : MvPowerSeries ι K) *
      (((k + l).choose k : ℕ) : MvPowerSeries ι K) =
      MvPowerSeries.C ((k.factorial : K)⁻¹) * MvPowerSeries.C ((l.factorial : K)⁻¹) := by
    rw [← map_natCast (MvPowerSeries.C : K →+* MvPowerSeries ι K), ← map_mul, ← map_mul]
    congr 1
    have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k l)
    rw [Nat.add_sub_cancel_left] at h1
    have h2 : (((k + l).choose k : ℕ) : K) * (k.factorial : K) * (l.factorial : K) =
        ((k + l).factorial : K) := by exact_mod_cast h1
    have hc : (((k + l).choose k : ℕ) : K) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.choose_pos (Nat.le_add_right k l)).ne'
    have hk0 : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
    have hl0 : (l.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 l.factorial_ne_zero
    rw [← h2]
    field_simp
  rw [Nat.add_sub_cancel_left]
  linear_combination (a ^ k * b ^ l) * key
end Formalism.InvariantFactorPaths.G7

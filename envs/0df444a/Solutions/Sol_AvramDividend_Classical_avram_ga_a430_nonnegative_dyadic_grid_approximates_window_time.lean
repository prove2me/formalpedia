-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a430_nonnegative_dyadic_grid_approximates_window_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:07:57.456212+00:00
-- url     : https://prove2.me/submissions/09df6dbf-757f-4acc-8bd3-e5c1c90fb7c6

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous
import Theorems.Thm_LevyStochCalc_Probability_tendsto_dyadicTime_dyadicIndex_readable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (T : ℝ≥0) (hT : 0 < T) (t : ℝ≥0) (ht : t ≤ T) :
    ∃ idx : ℕ → ℕ,
      (∀ k, idx k ≤ 2^k) ∧
      Filter.Tendsto
        (fun k : ℕ => (idx k : ℝ≥0) * T / (2^k : ℝ≥0))
        Filter.atTop (nhds t) := by
  classical
  let I : ℕ → ℕ := fun k =>
    LevyStochCalc.Probability.dyadicIndex (T : ℝ) (t : ℝ) k
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have htreal : (0 : ℝ) ≤ t := by positivity
  have htle : (t : ℝ) ≤ T := by exact_mod_cast ht
  have hI : ∀ k, I k ≤ 2 ^ k := by
    intro k
    dsimp [I, LevyStochCalc.Probability.dyadicIndex]
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hTreal).mpr
    have hpow : (0 : ℝ) ≤ 2 ^ k := by positivity
    have hmul := mul_le_mul_of_nonneg_right htle hpow
    simpa only [mul_comm, Nat.cast_pow, Nat.cast_ofNat] using hmul
  have htime (k : ℕ) :
      (I k : ℝ≥0) * T / (2 ^ k : ℝ≥0) =
        Real.toNNReal
          (LevyStochCalc.Probability.dyadicTime (T : ℝ) k (I k)) := by
    have hfrac : (I k : ℝ) * (T : ℝ) / (2 : ℝ)^k ≤ T := by
      apply (div_le_iff₀ (pow_pos (by norm_num) k)).mpr
      have hiR : (I k : ℝ) ≤ (2 : ℝ)^k := by exact_mod_cast hI k
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_right hiR (by positivity : (0 : ℝ) ≤ T))
    have hn : 0 ≤ (I k : ℝ) * (T : ℝ) / (2 : ℝ)^k := by positivity
    apply Subtype.ext
    change ((I k : ℝ) * (T : ℝ) / (2 : ℝ)^k) =
      ((Real.toNNReal
        (LevyStochCalc.Probability.dyadicTime (T : ℝ) k (I k))) : ℝ)
    rw [Real.coe_toNNReal]
    · simp [LevyStochCalc.Probability.dyadicTime, min_eq_left hfrac]
    · simpa [LevyStochCalc.Probability.dyadicTime, min_eq_left hfrac] using hn
  refine ⟨I, hI, ?_⟩
  have hreal := LevyStochCalc.Probability.tendsto_dyadicTime_dyadicIndex_readable
    hTreal htreal htle
  have hreal' : Filter.Tendsto
      (fun k => LevyStochCalc.Probability.dyadicTime (T : ℝ) k (I k))
      Filter.atTop (nhds (t : ℝ)) := by
    exact hreal.mono_right nhdsWithin_le_nhds
  have hNN := tendsto_real_toNNReal hreal'
  simpa only [Real.toNNReal_coe, ← htime] using hNN

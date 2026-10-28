-- Prove2me | solution 1 for AvramDividend.Classical.stopped_firstRecord_grid_pathwise_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:11:07.178746+00:00
-- url     : https://prove2.me/submissions/4e1f00f1-3463-4d51-8c15-f9a30536fb0a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_stopped_firstRecord_survived_prefix_discount_lower
import Theorems.Thm_AvramDividend_Classical_recordGrid_prefix_survival_weight_budget
import Theorems.Thm_AvramDividend_Classical_stopped_interval_reward_le_full_indicator
import Theorems.Thm_AvramDividend_Classical_firstRecord_finite_cell_budget_to_tsum
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_uniform_record_grid_mono
import Theorems.Thm_AvramDividend_Classical_chat08_named_upper_clock_eq_raw_infimum
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical
open AvramDividend.Classical
/-! Surviving record prefixes bound killed cells by the original Stieltjes payout. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a q b h : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hh : 0 < h) :
    (∑' n : ℕ,
      if twoSidedExitUpTime X (b + ((n + 1 : ℕ) : ℝ) * h) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (h * Real.exp
          (-(q * (twoSidedExitUpTime X (b + ((n + 1 : ℕ) : ℝ) * h) ω).toReal)))
      else 0) ≤
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) := by
  let τ : ℝ≥0∞ := barrierRuinTime X a ω
  let T : ℕ → ℝ≥0∞ :=
    fun n => twoSidedExitUpTime X (b + (n : ℝ) * h) ω
  let f : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Real.exp (-(q * (T (n + 1)).toReal))) * ENNReal.ofReal h
  let C : ℝ≥0∞ := ∫⁻ t,
    if t ∈ paymentTimes τ then ENNReal.ofReal (Real.exp (-(q * t))) else 0
    ∂(dividendMeasure (runningSup X) ω)
  have hmono : Monotone T := by
    simpa only [T, chat08_named_upper_clock_eq_raw_infimum] using
      firstUpcrossing_uniform_record_grid_mono X ω b h (le_of_lt hh)
  have hprefix (N : ℕ) (hSurvive : T N < τ) :
      (∑ n ∈ Finset.range N, f n) ≤ C := by
    have hgrid := stopped_firstRecord_survived_prefix_discount_lower
      X ω τ q b h hq hb hh N hSurvive
    have hinterval := stopped_interval_reward_le_full_indicator
      (dividendMeasure (runningSup X) ω) (paymentTimes τ)
      (paymentTimes_measurable τ) q (T 0).toReal (T N).toReal
    calc
      (∑ n ∈ Finset.range N, f n) ≤ _ := by simpa [f, T] using hgrid
      _ ≤ C := by simpa [T, C] using hinterval
  have hfinite (N : ℕ) :
      (∑ n ∈ Finset.range N,
        if T (n + 1) < τ then f n else 0) ≤ C :=
    recordGrid_prefix_survival_weight_budget T hmono τ f C hprefix N
  have htsum : (∑' n : ℕ, if T (n + 1) < τ then f n else 0) ≤ C :=
    firstRecord_finite_cell_budget_to_tsum
      (fun n => if T (n + 1) < τ then f n else 0) C hfinite
  have hf (n : ℕ) :
      ENNReal.ofReal (h * Real.exp (-(q * (T (n + 1)).toReal))) = f n := by
    dsimp [f]
    rw [ENNReal.ofReal_mul (le_of_lt hh)]
    exact mul_comm _ _
  have hsum :
      (∑' n : ℕ,
        if T (n + 1) < τ then
          ENNReal.ofReal (h * Real.exp (-(q * (T (n + 1)).toReal)))
        else 0) =
      (∑' n : ℕ, if T (n + 1) < τ then f n else 0) := by
    apply tsum_congr
    intro n
    by_cases hn : T (n + 1) < τ
    · simpa only [if_pos hn] using hf n
    · simp only [if_neg hn]
  change
    (∑' n : ℕ,
      if T (n + 1) < τ then
        ENNReal.ofReal (h * Real.exp (-(q * (T (n + 1)).toReal)))
      else 0) ≤ C
  exact hsum.le.trans htsum

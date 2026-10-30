-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_shifted_killed_record_grid_prefix_le_actual_stieltjes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:49:02.223688+00:00
-- url     : https://prove2.me/submissions/d77d65dd-3178-4713-b87f-f7c6244f6e9f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_Ioc_partition_fin
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_stopped_Ioc_discount_record_bounds_of_survival
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Each finite killed future-record cash mesh is bounded by its true
stopped shifted Stieltjes regulator payout, pathwise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (age : ℝ≥0)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (n N : ℕ) (hn : 0 < n) :
    let M : ℝ≥0 → ℝ := fun v =>
      sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
    let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
    let grid : ℕ → ℝ := fun j =>
      (((j : ℝ≥0) * (n : ℝ≥0)⁻¹) : ℝ)
    (∑ k ∈ Finset.range N,
      if ENNReal.ofReal (grid (k + 1)) < τ then
        ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) *
          ENNReal.ofReal
            (M (grid (k + 1)).toNNReal -
              M (grid k).toNNReal)
      else 0) ≤
    (∫⁻ r in paymentTimes τ,
      if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) := by
  let M : ℝ≥0 → ℝ := fun v =>
    sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
  let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
  let grid : ℕ → ℝ := fun j =>
    (((j : ℝ≥0) * (n : ℝ≥0)⁻¹) : ℝ)
  have hgmono : Monotone grid := by
    intro i j hij
    dsimp [grid]
    gcongr
  have heach (k : ℕ) :
      (if ENNReal.ofReal (grid (k + 1)) < τ then
          ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) *
            ENNReal.ofReal
              (M (grid (k + 1)).toNNReal -
                M (grid k).toNNReal)
        else 0) ≤
      (∫⁻ r in paymentTimes τ,
        if r ∈ Ioc (grid k) (grid (k + 1))
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) := by
    by_cases h : ENNReal.ofReal (grid (k + 1)) < τ
    · simp only [if_pos h]
      have h0 : 0 ≤ grid k := by dsimp [grid]; positivity
      have hSurv := paymentTimes_Ioc_subset_of_terminal_survival
        τ (grid k) (grid (k + 1)) h0 h
      exact (avram_root29_05_shifted_stopped_Ioc_discount_record_bounds_of_survival
        X ω age τ q hq (grid k) (grid (k + 1)) hSurv).1
    · simp only [if_neg h]
      exact bot_le
  have hparts := stopped_lintegral_Ioc_partition_fin
    μ (paymentTimes τ)
    (fun r : ℝ => ENNReal.ofReal (Real.exp (-(q * r))))
    grid hgmono N
  change (∑ k ∈ Finset.range N,
      if ENNReal.ofReal (grid (k + 1)) < τ then
        ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) *
          ENNReal.ofReal
            (M (grid (k + 1)).toNNReal -
              M (grid k).toNNReal)
      else 0) ≤ _
  calc
    _ ≤ ∑ k ∈ Finset.range N,
        (∫⁻ r in paymentTimes τ,
          if r ∈ Ioc (grid k) (grid (k + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) :=
          Finset.sum_le_sum (fun k _ => heach k)
    _ = (∫⁻ r in paymentTimes τ,
          if r ∈ Ioc (grid 0) (grid N)
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) := hparts.symm
    _ ≤ _ := by
      apply lintegral_mono
      intro r
      by_cases h : r ∈ Ioc (grid 0) (grid N)
      · have hp : 0 < r := by
          have hg0 : grid 0 = 0 := by simp [grid]
          simpa [hg0] using h.1
        simp [h, hp]
      · simp [h]

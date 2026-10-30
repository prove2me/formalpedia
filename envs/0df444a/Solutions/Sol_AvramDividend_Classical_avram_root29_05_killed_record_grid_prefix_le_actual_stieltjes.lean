-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_killed_record_grid_prefix_le_actual_stieltjes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:08:16.139709+00:00
-- url     : https://prove2.me/submissions/ca306cd9-9a6a-4da0-b1d6-8637a648bc80

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_Ioc_partition_fin
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_Ioc_discount_record_bounds_of_survival
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Every finite killed record-grid prefix is paid by the *actual* stopped
Stieltjes regulator, including the strict drawdown-ruin convention. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (n N : ℕ) (hn : 0 < n) :
    let grid : ℕ → ℝ := fun j =>
      (((j : ℝ≥0) * (n : ℝ≥0)⁻¹) : ℝ)
    (∑ k ∈ Finset.range N,
      if ENNReal.ofReal (grid (k + 1)) < τ then
        ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) *
          ENNReal.ofReal
            (runningSup X (grid (k + 1)).toNNReal ω -
              runningSup X (grid k).toNNReal ω)
      else 0) ≤
    (∫⁻ r in paymentTimes τ,
      if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) := by
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
              (runningSup X (grid (k + 1)).toNNReal ω -
                runningSup X (grid k).toNNReal ω)
        else 0) ≤
      (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (grid k) (grid (k + 1))
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) := by
    by_cases h : ENNReal.ofReal (grid (k + 1)) < τ
    · simp only [if_pos h]
      have h0 : 0 ≤ grid k := by dsimp [grid]; positivity
      have hSurv := paymentTimes_Ioc_subset_of_terminal_survival
        τ (grid k) (grid (k + 1)) h0 h
      exact (runningSup_stopped_Ioc_discount_record_bounds_of_survival
        X ω τ q hq (grid k) (grid (k + 1)) hSurv).1
    · simp only [if_neg h]
      exact bot_le
  have hparts := stopped_lintegral_Ioc_partition_fin
    (dividendMeasure (runningSup X) ω) (paymentTimes τ)
    (fun r : ℝ => ENNReal.ofReal (Real.exp (-(q * r))))
    grid hgmono N
  change (∑ k ∈ Finset.range N,
      if ENNReal.ofReal (grid (k + 1)) < τ then
        ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) *
          ENNReal.ofReal
            (runningSup X (grid (k + 1)).toNNReal ω -
              runningSup X (grid k).toNNReal ω)
      else 0) ≤ _
  calc
    _ ≤ ∑ k ∈ Finset.range N,
        (∫⁻ r in paymentTimes τ,
          if r ∈ Set.Ioc (grid k) (grid (k + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) :=
          Finset.sum_le_sum (fun k _ => heach k)
    _ = (∫⁻ r in paymentTimes τ,
          if r ∈ Set.Ioc (grid 0) (grid N)
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) := hparts.symm
    _ ≤ _ := by
      apply lintegral_mono
      intro r
      by_cases h : r ∈ Set.Ioc (grid 0) (grid N)
      · have hp : 0 < r := by
          have hg0 : grid 0 = 0 := by simp [grid]
          simpa [hg0] using h.1
        simp [h, hp]
      · simp [h]

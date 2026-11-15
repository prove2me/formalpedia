-- Prove2me | solution 1 for AvramDividend.Classical.avram_b106_original_initial_event_masked_negative_grid_compensator_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:41:51.492615+00:00
-- url     : https://prove2.me/submissions/aeca81ca-aa0f-44bd-8a60-b05eb4b0b086

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_stopped_predictable_grid_L2_zero_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A predictable initial event preserves exact original stopped finite-grid negative-cutoff centring. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (A : Set Ω)
    (hA : ∀ i, MeasurableSet[𝓕.rightCont (grid i)] A)
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (n : ℕ) :
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    (∫ ω, ∑ i ∈ Finset.range n,
      (if ω ∈ A then
         (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω)
       else 0) * ((N i ω).toReal - r i) ∂P) = 0 := by
  classical
  let H' : ℕ → Ω → ℝ := fun i ω => if ω ∈ A then H i ω else 0
  have hH' (i : ℕ) :
      StronglyMeasurable[𝓕.rightCont (grid i)] (H' i) := by
    exact ((hH i).measurable.ite (hA i) measurable_const).stronglyMeasurable
  have hBound' : ∀ i ω, |H' i ω| ≤ L := by
    intro i ω
    by_cases h : ω ∈ A
    · simpa [H', h] using hBound i ω
    · have hL : 0 ≤ L := le_trans (abs_nonneg _) (hBound i ω)
      simpa [H', h] using hL
  have hMean :=
    (avram_p4_s3_interval_h_original_full_cutoff_stopped_predictable_grid_L2_zero_mean
      X cut τ hτstop grid hGrid H' hH' L hBound' n).2
  convert hMean using 1
  apply integral_congr_ae
  filter_upwards [] with ω
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : ω ∈ A
  · simp only [H', if_pos h, ite_mul, zero_mul]
  · simp [H', h]

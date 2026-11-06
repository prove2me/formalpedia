-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_stopped_predictable_grid_L2_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:47:18.69518+00:00
-- url     : https://prove2.me/submissions/b0594eff-afdb-494a-8da8-18a505c40c8b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_predictable_finite_grid_L2_zero_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
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
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    MemLp (fun ω => ∑ i ∈ Finset.range n, Z i ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0 := by
  classical
  let W : ℕ → Ω → ℝ := fun i ω =>
    if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
    then (0 : ℝ) else H i ω
  have hWsm (i : ℕ) :
      StronglyMeasurable[𝓕.rightCont (grid i)] (W i) := by
    have hs : MeasurableSet[𝓕.rightCont (grid i)]
        {ω : Ω | (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)} :=
      hτstop (grid i)
    exact StronglyMeasurable.ite hs stronglyMeasurable_const (hH i)
  have hWbound (i : ℕ) (ω : Ω) : |W i ω| ≤ L := by
    by_cases hs : (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
    · simpa only [W, if_pos hs, abs_zero] using
        (abs_nonneg (H i ω)).trans (hBound i ω)
    · simpa only [W, if_neg hs] using hBound i ω
  simpa only [W] using
    (avram_p4_s3_interval_h_original_full_cutoff_predictable_finite_grid_L2_zero_mean
      X cut grid hGrid W hWsm L hWbound n)

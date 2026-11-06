-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_run1750_original_full_cutoff_rightcont_finite_grid_diagonal_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:00:44.071765+00:00
-- url     : https://prove2.me/submissions/18b7d2d9-2334-432b-9362-3e61bc6a6756

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_predictable_L2_isometry_auto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Exact diagonal L² energy of the original physical negative-jump grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
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
      H i ω * ((N i ω).toReal - r i)
    Integrable (fun ω => ∑ i ∈ Finset.range n, (Z i ω)^2) P ∧
      (∫ ω, ∑ i ∈ Finset.range n, (Z i ω)^2 ∂P) =
        ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω)^2 ∂P := by
  classical
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
  let Z : ℕ → Ω → ℝ := fun i ω => H i ω * ((N i ω).toReal - r i)
  change Integrable (fun ω => ∑ i ∈ Finset.range n, (Z i ω)^2) P ∧
    (∫ ω, ∑ i ∈ Finset.range n, (Z i ω)^2 ∂P) =
      ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω)^2 ∂P
  have hCell (i : ℕ) : MemLp (Z i) 2 P ∧
      (∫ ω, (Z i ω)^2 ∂P) = r i * ∫ ω, (H i ω)^2 ∂P := by
    have hStep :=
      avram_p4_s3_interval_h_original_full_cutoff_bounded_predictable_L2_isometry_auto
        X (grid i) (grid (i + 1) - grid i) cut
        (H i) (hH i) L (hBound i)
    have hWindow : grid i + (grid (i + 1) - grid i) =
        grid (i + 1) := add_tsub_cancel_of_le (hGrid i)
    constructor
    · simpa only [Z, N, r, hWindow] using hStep.1
    · simpa only [Z, N, r, hWindow] using hStep.2
  have hInt (i : ℕ) : Integrable (fun ω => (Z i ω)^2) P :=
    (hCell i).1.integrable_sq
  constructor
  · have hSum := integrable_finset_sum (Finset.range n)
      (fun i hi => hInt i)
    simpa only [Finset.sum_apply] using hSum
  · rw [integral_finset_sum (Finset.range n) (fun i hi => hInt i)]
    exact Finset.sum_congr rfl (fun i hi => (hCell i).2)

-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_run1750_original_full_cutoff_rightcont_grid_diagonal_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:10:13.501757+00:00
-- url     : https://prove2.me/submissions/21738deb-ca5f-4818-89ee-1065bac07021

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1750_original_full_cutoff_rightcont_finite_grid_diagonal_energy
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
    (L : ℝ) (hL : 0 ≤ L) (hBound : ∀ i ω, |H i ω| ≤ L)
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
    (∫ ω, ∑ i ∈ Finset.range n, (Z i ω)^2 ∂P) ≤
      (∑ i ∈ Finset.range n, r i) * L^2 := by
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
  change (∫ ω, ∑ i ∈ Finset.range n, (Z i ω)^2 ∂P) ≤
    (∑ i ∈ Finset.range n, r i) * L^2
  have hExact :=
    (avram_p4_s3_run1750_original_full_cutoff_rightcont_finite_grid_diagonal_energy
      X cut grid hGrid H hH L hBound n).2
  change (∫ ω, ∑ i ∈ Finset.range n, (Z i ω)^2 ∂P) =
    ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω)^2 ∂P at hExact
  rw [hExact]
  calc
    (∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω)^2 ∂P)
        ≤ ∑ i ∈ Finset.range n, r i * L^2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left
      · have hGlobalSM : StronglyMeasurable (H i) :=
          (hH i).mono (𝓕.rightCont.le (grid i))
        have hLp : MemLp (H i) 2 P :=
          MemLp.of_bound hGlobalSM.aestronglyMeasurable L
            (Filter.Eventually.of_forall (fun ω => by
              simpa only [Real.norm_eq_abs] using hBound i ω))
        have hBdd (ω : Ω) : (H i ω)^2 ≤ L^2 := by
          have hprod : 0 ≤ (L - |H i ω|) * (L + |H i ω|) :=
            mul_nonneg (sub_nonneg.mpr (hBound i ω))
              (add_nonneg hL (abs_nonneg _))
          nlinarith [sq_abs (H i ω)]
        have hle := integral_mono (hLp.integrable_sq)
          (integrable_const (L^2)) hBdd
        simpa using hle
      · change 0 ≤ (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
        exact ENNReal.toReal_nonneg
    _ = (∑ i ∈ Finset.range n, r i) * L^2 := by
      rw [Finset.sum_mul]

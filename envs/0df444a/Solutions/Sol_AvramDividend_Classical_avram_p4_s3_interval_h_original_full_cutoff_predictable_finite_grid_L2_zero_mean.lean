-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_predictable_finite_grid_L2_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:40:51.727294+00:00
-- url     : https://prove2.me/submissions/2131ba45-390a-4c73-92bb-ce051d0fc965

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_conditional_martingale_step
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
    MemLp (fun ω => ∑ i ∈ Finset.range n, Z i ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0 := by
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
  change MemLp (fun ω => ∑ i ∈ Finset.range n, Z i ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0
  have hCell (i : ℕ) :
      MemLp (Z i) 2 P ∧ (∫ ω, Z i ω ∂P) = 0 := by
    have hStep :=
      avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_conditional_martingale_step
        X (grid i) (grid (i + 1) - grid i) cut
        (H i) (hH i) L (hBound i)
    have hWindow : grid i + (grid (i + 1) - grid i) =
        grid (i + 1) := add_tsub_cancel_of_le (hGrid i)
    constructor
    · simpa only [Z, N, r, hWindow] using hStep.1
    · simpa only [Z, N, r, hWindow] using hStep.2.2
  have hSum (S : Finset ℕ) : MemLp (∑ i ∈ S, Z i) 2 P := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a R ha ih =>
      simpa only [Finset.sum_insert ha] using (hCell a).1.add ih
  have hPointwise (S : Finset ℕ) :
      (∑ i ∈ S, Z i) = fun ω => ∑ i ∈ S, Z i ω := by
    funext ω
    simp only [Finset.sum_apply]
  constructor
  · rw [← hPointwise]
    exact hSum (Finset.range n)
  · rw [integral_finset_sum (Finset.range n)
        (by intro i hi; exact (hCell i).1.integrable (by norm_num))]
    have hMean (i : ℕ) : (∫ ω, Z i ω ∂P) = 0 := (hCell i).2
    simp only [hMean, Finset.sum_const_zero]

-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_weighted_R_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:20:50.530389+00:00
-- url     : https://prove2.me/submissions/27fbaf08-d7c1-4edc-ab01-721554e1dd8b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The literal original-process bounded-variation residual can be controlled on
any finite physical mesh by its total variation, once its predictable weights
are bounded. This estimate is entirely pathwise, so it introduces no Brownian
or equality-in-law assumptions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (a : ℕ → ℝ) (K : ℝ)
    (hK : ∀ i ∈ Finset.range (n + 1), |a i| ≤ K) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    |∑ i ∈ Finset.range (n + 1),
        a i * (R (u n i) - R (u n (i + 1)))| ≤
      K * ∑ i ∈ Finset.range (n + 1),
        |R (u n i) - R (u n (i + 1))| := by
  classical
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
    else 0
  let R : ℝ≥0 → ℝ := fun t =>
    ((t : ℝ) * X.drift - X.X t ω) - J t
  change |∑ i ∈ Finset.range (n + 1),
      a i * (R (u n i) - R (u n (i + 1)))| ≤
    K * ∑ i ∈ Finset.range (n + 1),
      |R (u n i) - R (u n (i + 1))|
  calc
    |∑ i ∈ Finset.range (n + 1),
        a i * (R (u n i) - R (u n (i + 1)))| ≤
        ∑ i ∈ Finset.range (n + 1),
          |a i * (R (u n i) - R (u n (i + 1)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (n + 1),
          |a i| * |R (u n i) - R (u n (i + 1))| := by
      simp only [abs_mul]
    _ ≤ ∑ i ∈ Finset.range (n + 1),
          K * |R (u n i) - R (u n (i + 1))| := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hK i hi) (abs_nonneg _)
    _ = K * ∑ i ∈ Finset.range (n + 1),
          |R (u n i) - R (u n (i + 1))| := by
      rw [Finset.mul_sum]

-- Prove2me | solution 1 for AvramDividend.Classical.avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:28:08.174666+00:00
-- url     : https://prove2.me/submissions/2336532b-e2d7-4991-a585-8c8e81d50f48

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Physical compact mixed Gaussian and negative jump-cell squared source increment comparison. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (J : Ω → Finset ℕ)
    (A : Set Ω) (d a b : ℝ) (hab : a ≤ b)
    (hNoJump : ∀ ω ∈ A, ∀ i ∈ S, i ∉ J ω →
      X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
          V i ω + d * ((t i ω - s i ω : ℝ≥0) : ℝ))
    (hJump : ∀ ω ∈ A, ∀ i ∈ S, i ∈ J ω →
      |X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c| ≤ b - a) :
    ∀ ω ∈ A,
      (∑ i ∈ S,
        (X.X (t i ω) ω - X.X (s i ω) ω -
          ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2) ≤
      ∑ i ∈ S,
        (2 * (V i ω)^2 +
          2 * d^2 * (((t i ω - s i ω : ℝ≥0) : ℝ))^2 +
          if i ∈ J ω then (b-a)^2 else 0) := by 
  classical
  intro ω hω
  let g : ℕ → ℝ := fun i =>
    X.X (t i ω) ω - X.X (s i ω) ω -
      ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c
  let δ : ℕ → ℝ := fun i => ((t i ω - s i ω : ℝ≥0) : ℝ)
  have hb : 0 ≤ b - a := sub_nonneg.mpr hab
  apply Finset.sum_le_sum
  intro i hi
  change (g i)^2 ≤ 2 * (V i ω)^2 +
    2 * d^2 * (δ i)^2 + if i ∈ J ω then (b-a)^2 else 0
  by_cases hj : i ∈ J ω
  · simp only [if_pos hj]
    have hbound := hJump ω hω i hi hj
    have habs : |g i| ≤ b - a := hbound
    have hsq : (g i)^2 ≤ (b-a)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr habs)
        (add_nonneg (abs_nonneg (g i)) hb), sq_abs (g i)]
    nlinarith [sq_nonneg (V i ω), sq_nonneg (d * δ i)]
  · simp only [if_neg hj, add_zero]
    have heq : g i = V i ω + d * δ i :=
      hNoJump ω hω i hi hj
    rw [heq]
    nlinarith [sq_nonneg (V i ω - d * δ i)]

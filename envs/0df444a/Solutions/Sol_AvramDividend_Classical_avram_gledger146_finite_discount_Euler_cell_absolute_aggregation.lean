-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger146_finite_discount_Euler_cell_absolute_aggregation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:00:53.066022+00:00
-- url     : https://prove2.me/submissions/9f0886be-7c9e-4b53-ab95-c53478202b23

import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section
theorem solution
    (m : ℕ) (q δ K : ℝ) (s weight : ℕ → ℝ)
    (hK : 0 ≤ K)
    (hw : ∀ i ∈ Finset.range m, |weight i| ≤ K)
    (hcell : ∀ i ∈ Finset.range m,
      |Real.exp (-(q * (s i + δ))) - Real.exp (-(q * s i)) +
        q * δ * Real.exp (-(q * s i))| ≤ (q * δ) ^ 2) :
    |∑ i ∈ Finset.range m,
      (Real.exp (-(q * (s i + δ))) - Real.exp (-(q * s i)) +
        q * δ * Real.exp (-(q * s i))) * weight i| ≤
        (m : ℝ) * ((q * δ) ^ 2 * K) := by
  have hterm (i : ℕ) (hi : i ∈ Finset.range m) :
      |(Real.exp (-(q * (s i + δ))) - Real.exp (-(q * s i)) +
        q * δ * Real.exp (-(q * s i))) * weight i| ≤
      (q * δ) ^ 2 * K := by
    rw [abs_mul]
    calc
      _ ≤ (q * δ) ^ 2 * |weight i| :=
        mul_le_mul_of_nonneg_right (hcell i hi) (abs_nonneg _)
      _ ≤ (q * δ) ^ 2 * K :=
        mul_le_mul_of_nonneg_left (hw i hi) (sq_nonneg _)
  calc
    |∑ i ∈ Finset.range m,
      (Real.exp (-(q * (s i + δ))) - Real.exp (-(q * s i)) +
        q * δ * Real.exp (-(q * s i))) * weight i| ≤
        ∑ i ∈ Finset.range m,
        |(Real.exp (-(q * (s i + δ))) - Real.exp (-(q * s i)) +
          q * δ * Real.exp (-(q * s i))) * weight i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range m, (q * δ) ^ 2 * K :=
      Finset.sum_le_sum (fun i hi => hterm i hi)
    _ = (m : ℝ) * ((q * δ) ^ 2 * K) := by simp [mul_comm]

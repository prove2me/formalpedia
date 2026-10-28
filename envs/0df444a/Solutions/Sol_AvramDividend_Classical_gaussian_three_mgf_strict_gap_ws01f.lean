-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_three_mgf_strict_gap_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:53:48.285624+00:00
-- url     : https://prove2.me/submissions/c28d408e-0a9a-48f8-aa7b-9b9e8f74b29a

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open Filter
open scoped Topology

theorem solution (a : ℝ) (ha : 0 < a) :
    ∃ m : ℕ, 0 < m ∧
      (m : ℝ) ^ 2 *
          (Real.exp (a / ((m : ℝ) ^ 2)) - 1) +
        (Real.exp (4 * a) - 1) / (m : ℝ) <
          Real.exp a - 1 := by
  have hD : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hA : Tendsto (fun n : ℕ =>
      a * ((1 : ℝ) / ((n : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
    simpa using (hD.pow 2).const_mul a
  have hExp : Tendsto (fun n : ℕ =>
      Real.exp (a * ((1 : ℝ) / ((n : ℝ) + 1)) ^ 2))
      atTop (𝓝 1) := by
    have hh := Real.continuous_exp.continuousAt.tendsto.comp hA
    change Tendsto (fun n : ℕ =>
      Real.exp (a * ((1 : ℝ) / ((n : ℝ) + 1)) ^ 2))
      atTop (𝓝 (Real.exp 0)) at hh
    simpa only [Real.exp_zero] using hh
  have hLim : Tendsto (fun n : ℕ =>
      a * Real.exp (a * ((1 : ℝ) / ((n : ℝ) + 1)) ^ 2) +
        (Real.exp (4 * a) - 1) *
          ((1 : ℝ) / ((n : ℝ) + 1)))
      atTop (𝓝 a) := by
    simpa only [mul_one, mul_zero, add_zero] using
      (hExp.const_mul a).add (hD.const_mul (Real.exp (4 * a) - 1))
  have hStrict : a < Real.exp a - 1 := by
    have h := Real.add_one_lt_exp (ne_of_gt ha)
    linarith
  have he : ∀ᶠ n : ℕ in atTop,
      a * Real.exp (a * ((1 : ℝ) / ((n : ℝ) + 1)) ^ 2) +
        (Real.exp (4 * a) - 1) *
          ((1 : ℝ) / ((n : ℝ) + 1)) < Real.exp a - 1 :=
    hLim.eventually (Iio_mem_nhds hStrict)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  refine ⟨N + 1, by omega, ?_⟩
  have hd : 0 < (N : ℝ) + 1 := by positivity
  have hNeg := Real.add_one_le_exp (-(a / (((N : ℝ) + 1) ^ 2)))
  have hmult :=
    mul_le_mul_of_nonneg_right hNeg
      (Real.exp_pos (a / (((N : ℝ) + 1) ^ 2))).le
  have hCancel :
      Real.exp (-(a / (((N : ℝ) + 1) ^ 2))) *
        Real.exp (a / (((N : ℝ) + 1) ^ 2)) = 1 := by
    rw [Real.exp_neg]
    exact inv_mul_cancel₀ (ne_of_gt (Real.exp_pos _))
  have hLin :
      Real.exp (a / (((N : ℝ) + 1) ^ 2)) - 1 ≤
        (a / (((N : ℝ) + 1) ^ 2)) *
          Real.exp (a / (((N : ℝ) + 1) ^ 2)) := by
    rw [hCancel] at hmult
    nlinarith [hmult]
  have hBound :
      (((N : ℝ) + 1) ^ 2) *
          (Real.exp (a / (((N : ℝ) + 1) ^ 2)) - 1) ≤
        a * Real.exp (a / (((N : ℝ) + 1) ^ 2)) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hLin (sq_nonneg ((N : ℝ) + 1))
    have hid2 : (((N : ℝ) + 1) ^ 2) *
        ((a / (((N : ℝ) + 1) ^ 2)) *
          Real.exp (a / (((N : ℝ) + 1) ^ 2))) =
        a * Real.exp (a / (((N : ℝ) + 1) ^ 2)) := by
      field_simp [ne_of_gt hd] <;> ring
    calc
      _ ≤ (((N : ℝ) + 1) ^ 2) *
        ((a / (((N : ℝ) + 1) ^ 2)) *
          Real.exp (a / (((N : ℝ) + 1) ^ 2))) := hmul
      _ = _ := hid2
  have hExpID :
      a * ((1 : ℝ) / ((N : ℝ) + 1)) ^ 2 =
        a / (((N : ℝ) + 1) ^ 2) := by
    field_simp [ne_of_gt hd] <;> ring
  rw [Nat.cast_add, Nat.cast_one]
  have hN' := hN N le_rfl
  rw [hExpID] at hN'
  have hEnd : (Real.exp (4 * a) - 1) *
      ((1 : ℝ) / ((N : ℝ) + 1)) =
        (Real.exp (4 * a) - 1) / ((N : ℝ) + 1) := by ring
  rw [hEnd] at hN'
  linarith [hBound, hN']

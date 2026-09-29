-- Prove2me | solution 2 for ErlerGross.B3_cubic_reciprocal_series_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T16:27:08.275356+00:00
-- url     : https://prove2.me/submissions/55efa0cb-3ccb-4d5c-8b95-aeda0227ceeb

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

lemma eg_b3_harmonic_diff_tendsto (k c : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => ((harmonic (k * N + c) : ℚ) : ℝ) -
      ((harmonic N : ℚ) : ℝ)) atTop (𝓝 (Real.log k)) := by
  have hkN : Tendsto (fun N : ℕ => k * N + c) atTop atTop := by
    apply tendsto_atTop_mono (fun N => by
      exact (Nat.le_mul_of_pos_left N (Nat.zero_lt_of_lt hk)).trans
        (Nat.le_add_right (k * N) c))
    exact tendsto_id
  have h1 := Real.tendsto_harmonic_sub_log_add_one.comp hkN
  have h2 := Real.tendsto_harmonic_sub_log_add_one
  have h3 : Tendsto
      (fun N : ℕ => Real.log ((k : ℝ) + ((c : ℝ) + 1 - k) *
        (1 / ((N : ℝ) + 1)))) atTop (𝓝 (Real.log k)) := by
    have hk0 : (k : ℝ) ≠ 0 := by
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have h :=
      ((tendsto_one_div_add_atTop_nhds_zero_nat).const_mul
        ((c : ℝ) + 1 - k)).const_add (k : ℝ)
    rw [mul_zero, add_zero] at h
    exact h.log hk0
  have hsum := (h1.sub h2).add h3
  rw [sub_self, zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards with N
  simp only [Function.comp]
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have harg : (k : ℝ) + ((c : ℝ) + 1 - k) * (1 / ((N : ℝ) + 1)) =
      ((((k * N + c : ℕ) : ℝ) + 1)) / ((N : ℝ) + 1) := by
    push_cast
    field_simp
    ring
  rw [harg, Real.log_div (by positivity) (by positivity)]
  ring

lemma eg_b3_partial_sum (N : ℕ) :
    ∑ n ∈ Finset.range N,
      1 / (((2 * (n : ℝ) + 1) * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))) =
      3 * ((harmonic (3 * N) : ℚ) : ℝ) -
        4 * ((harmonic (2 * N) : ℚ) : ℝ) + ((harmonic N : ℚ) : ℝ) := by
  induction N with
  | zero => simp [harmonic]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have e3 : 3 * (N + 1) = (3 * N) + 1 + 1 + 1 := by ring
    have e2 : 2 * (N + 1) = (2 * N) + 1 + 1 := by ring
    rw [e3, e2, harmonic_succ (3 * N + 1 + 1),
      harmonic_succ (3 * N + 1), harmonic_succ (3 * N),
      harmonic_succ (2 * N + 1), harmonic_succ (2 * N), harmonic_succ N]
    push_cast
    have h1 : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < 3 * (N : ℝ) + 1 := by positivity
    have h3 : (0 : ℝ) < 3 * (N : ℝ) + 2 := by positivity
    have h4 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    field_simp [ne_of_gt h1, ne_of_gt h2, ne_of_gt h3, ne_of_gt h4]
    ring

lemma eg_b3_log_identity :
    Real.log (27 / 16) = 3 * Real.log 3 - 4 * Real.log 2 := by
  calc
    Real.log (27 / 16) = Real.log ((3 : ℝ) ^ 3 / (2 : ℝ) ^ 4) := by norm_num
    _ = Real.log ((3 : ℝ) ^ 3) - Real.log ((2 : ℝ) ^ 4) := by
      rw [Real.log_div] <;> norm_num
    _ = 3 * Real.log 3 - 4 * Real.log 2 := by
      rw [Real.log_pow, Real.log_pow]
      norm_num

theorem solution :
    HasSum (fun n : Nat =>
      1 / (((2 * (n : Real) + 1) * (3 * (n : Real) + 1) * (3 * (n : Real) + 2))))
      (Real.log (27 / 16)) := by
  have hnn : ∀ n : ℕ, 0 ≤
      1 / (((2 * (n : ℝ) + 1) * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))) := by
    intro n
    have h1 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < 3 * (n : ℝ) + 1 := by positivity
    have h3 : (0 : ℝ) < 3 * (n : ℝ) + 2 := by positivity
    positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have h3 := (eg_b3_harmonic_diff_tendsto 3 0 (by norm_num)).const_mul (3 : ℝ)
  have h2 := (eg_b3_harmonic_diff_tendsto 2 0 (by norm_num)).const_mul (-4 : ℝ)
  have h := h3.add h2
  have h' : Tendsto (fun N : ℕ =>
      3 * (((harmonic (3 * N) : ℚ) : ℝ) - ((harmonic N : ℚ) : ℝ)) +
        (-4) * (((harmonic (2 * N) : ℚ) : ℝ) - ((harmonic N : ℚ) : ℝ))) atTop
      (𝓝 (3 * Real.log 3 - 4 * Real.log 2)) := by
    convert h using 1 <;> ring
  convert h' using 1
  · funext N
    rw [eg_b3_partial_sum]
    ring
  · rw [eg_b3_log_identity]

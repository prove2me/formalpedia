-- Prove2me | solution 3 for ErlerGross.B3_cubic_reciprocal_series_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T16:28:20.486485+00:00
-- url     : https://prove2.me/submissions/afeb43a5-22b2-4821-a208-8d8145ed03aa

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

theorem solution :
    HasSum (fun n : Nat => 1 / (((2 * (n : Real) + 1) * (3 * (n : Real) + 1) * (3 * (n : Real) + 2))))
      (Real.log (27 / 16)) := by
  have harm_diff_tendsto : ∀ (k c : ℕ), 1 ≤ k →
      Tendsto (fun N : ℕ => ((harmonic (k * N + c) : ℚ) : ℝ) - ((harmonic N : ℚ) : ℝ))
        atTop (𝓝 (Real.log k)) := by
    intro k c hk
    have hkN : Tendsto (fun N : ℕ => k * N + c) atTop atTop := by
      apply tendsto_atTop_mono (fun N => (by nlinarith : N ≤ k * N + c))
      exact tendsto_id
    have h1 := tendsto_harmonic_sub_log_add_one.comp hkN
    have h2 := tendsto_harmonic_sub_log_add_one
    have h3 : Tendsto (fun N : ℕ => Real.log ((k : ℝ) + ((c : ℝ) + 1 - k) * (1 / ((N : ℝ) + 1))))
        atTop (𝓝 (Real.log k)) := by
      have hk0 : (k : ℝ) ≠ 0 := by
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have ht := ((tendsto_one_div_add_atTop_nhds_zero_nat).const_mul ((c : ℝ) + 1 - k)).const_add (k : ℝ)
      rw [mul_zero, add_zero] at ht
      exact ht.log hk0
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
      ring_nf
    rw [harg, Real.log_div (by positivity) (by positivity)]
    ring_nf
  have hpartial : ∀ N : ℕ,
      ∑ n ∈ Finset.range N, 1 / (((2 * (n : ℝ) + 1) * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))) =
        -4 * ((harmonic (2 * N) : ℚ) : ℝ) + ((harmonic N : ℚ) : ℝ) +
          3 * ((harmonic (3 * N) : ℚ) : ℝ) := by
    intro N
    induction N with
    | zero => simp [harmonic]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have e2 : 2 * (N + 1) = 2 * N + 2 := by ring
      have e3 : 3 * (N + 1) = 3 * N + 3 := by ring
      rw [e2, e3, harmonic_succ (2 * N + 1), harmonic_succ (2 * N),
        harmonic_succ (N), harmonic_succ (3 * N + 2), harmonic_succ (3 * N + 1),
        harmonic_succ (3 * N)]
      push_cast
      field_simp
      ring_nf
  have hnn : ∀ n : ℕ, 0 ≤ 1 / (((2 * (n : ℝ) + 1) * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2))) := by
    intro n
    positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have h2 := harm_diff_tendsto 2 0 (by norm_num)
  have h3 := harm_diff_tendsto 3 0 (by norm_num)
  have h := (h2.const_mul (-4)).add (h3.const_mul 3)
  convert h using 2 with N
  · rw [hpartial]
    ring_nf
  · push_cast
    have harg : (27 / 16 : ℝ) = (3 : ℝ) ^ 3 / (2 : ℝ) ^ 4 := by norm_num
    rw [harg, Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring_nf

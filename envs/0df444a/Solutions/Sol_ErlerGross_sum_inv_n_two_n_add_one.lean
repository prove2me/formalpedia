-- Prove2me | solution 1 for ErlerGross.sum_inv_n_two_n_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T13:15:42.806322+00:00
-- url     : https://prove2.me/submissions/9d1ab383-aefa-4861-b56c-4b71121ed4de

import Mathlib
import Definitions.Def_ErlerGross_defs

set_option autoImplicit false

open Real Filter Topology

theorem eg2fde_harm_diff_tendsto (k c : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => ((harmonic (k * N + c) : ℚ) : ℝ) - ((harmonic N : ℚ) : ℝ))
      atTop (𝓝 (Real.log k)) := by
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
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat).const_mul ((c : ℝ) + 1 - k)).const_add (k : ℝ)
    rw [mul_zero, add_zero] at this
    exact this.log hk0
  have hsum := (h1.sub h2).add h3
  rw [sub_self, zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards with N
  simp only [Function.comp]
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have harg : (k : ℝ) + ((c : ℝ) + 1 - k) * (1 / ((N : ℝ) + 1)) =
      ((((k * N + c : ℕ) : ℝ) + 1)) / ((N : ℝ) + 1) := by
    push_cast
    field_simp
    ring
  rw [harg, Real.log_div (by positivity) (by positivity)]
  ring

theorem eg2fde_partial (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / (((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) + 1)) =
      2 + 2 * ((harmonic N : ℚ) : ℝ) - 2 * ((harmonic (2 * N + 1) : ℚ) : ℝ) := by
  induction N with
  | zero => simp [harmonic]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have e : 2 * (N + 1) + 1 = (2 * N + 1) + 1 + 1 := by ring
    rw [e, harmonic_succ N, harmonic_succ (2 * N + 1 + 1), harmonic_succ (2 * N + 1)]
    push_cast
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    field_simp
    ring

open Real Filter Topology MeasureTheory ErlerGross in
theorem solution :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) + 1)))
      (2 - 2 * Real.log 2) := by
  have hnn : ∀ n : ℕ, 0 ≤ 1 / (((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) + 1)) :=
    fun n => by positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have h := ((eg2fde_harm_diff_tendsto 2 1 (by norm_num)).const_mul (-2)).const_add 2
  have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [e2] at h
  convert h using 2 with N
  · rw [eg2fde_partial]; ring
  · ring

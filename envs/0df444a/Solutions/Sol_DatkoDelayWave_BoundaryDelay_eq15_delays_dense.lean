-- Prove2me | solution 1 for DatkoDelayWave.BoundaryDelay.eq15_delays_dense
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:00:56.344457+00:00
-- url     : https://prove2.me/submissions/98fc2ba8-a356-4ee7-91d4-9c3f75edfe1e

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

open DatkoDelayWave.BoundaryDelay in
theorem solution :
    Set.Ioi (0 : ℝ) ⊆
      closure {ε : ℝ | ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧
            ε = 2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1)} := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  rw [Metric.mem_closure_iff]
  intro e he
  obtain ⟨n, hn⟩ := exists_nat_gt (4 / e + 2 / x + 1)
  have h4e : 0 ≤ 4 / e := by positivity
  have h2x : 0 ≤ 2 / x := by positivity
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hnpos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by linarith
  set t : ℝ := (x * (2 * (n : ℝ) + 1) / 2 - 1) / 2 with ht
  have hxn : 2 < x * (2 * (n : ℝ) + 1) := by
    have : 2 / x < n := by linarith
    rw [div_lt_iff₀ hx0] at this
    nlinarith
  have htpos : 0 < t := by rw [ht]; linarith
  set m : ℕ := ⌈t⌉₊ with hm
  have hm1 : t ≤ (m : ℝ) := Nat.le_ceil t
  have hm2 : (m : ℝ) < t + 1 := Nat.ceil_lt_add_one htpos.le
  have hmge : 1 ≤ m := by
    rw [hm]; exact Nat.one_le_iff_ne_zero.mpr (by
      intro h; rw [Nat.ceil_eq_zero] at h; linarith)
  refine ⟨2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1), ⟨m, n, hmge, by exact_mod_cast (show (1:ℝ) ≤ n from hn1), rfl⟩, ?_⟩
  rw [Real.dist_eq, abs_lt]
  have hen : 4 / (2 * (n : ℝ) + 1) < e := by
    rw [div_lt_iff₀ hnpos]
    have : 4 / e < n := by linarith
    rw [div_lt_iff₀ he] at this
    nlinarith
  have key1 : x ≤ 2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1) := by
    rw [le_div_iff₀ hnpos]; rw [ht] at hm1; linarith
  have key2 : 2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1) < x + 4 / (2 * (n : ℝ) + 1) := by
    have : x + 4 / (2 * (n : ℝ) + 1) = (x * (2 * (n : ℝ) + 1) + 4) / (2 * (n : ℝ) + 1) := by
      field_simp
    rw [this, div_lt_div_iff_of_pos_right hnpos]
    rw [ht] at hm2; linarith
  constructor <;> linarith

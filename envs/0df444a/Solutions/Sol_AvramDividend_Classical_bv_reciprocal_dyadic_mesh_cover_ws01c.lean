-- Prove2me | solution 1 for AvramDividend.Classical.bv_reciprocal_dyadic_mesh_cover_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:04:41.509334+00:00
-- url     : https://prove2.me/submissions/c947d528-cdda-4a99-9709-467764f52eb9

import Mathlib
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_exists_dyadic_scale_readable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped NNReal

theorem solution
    (N : ℕ) (t : ℝ≥0)
    (ht : 0 < t) (htN : t < ((1 : ℝ≥0) / 2) ^ N) :
    ∃ n : ℕ,
      N ≤ n ∧ ((1 : ℝ≥0) / 2) ^ (n + 1) ≤ t ∧
      t ≤ ((1 : ℝ≥0) / 2) ^ n := by
  have hq : (1 : ℝ≥0) / 2 ≤ 1 := by norm_num
  have hStep (n : ℕ) :
      ((1 : ℝ≥0) / 2) ^ (n + 1) ≤ ((1 : ℝ≥0) / 2) ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (by positivity) _) hq
  have hAnti : Antitone (fun n : ℕ => ((1 : ℝ≥0) / 2) ^ n) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact le_rfl
    | succ m hnm ih => exact (hStep m).trans ih
  have htOne : t ≤ 1 := by
    have h := (le_of_lt htN).trans (hAnti (Nat.zero_le N))
    simpa only [pow_zero] using h
  have htReal0 : 0 < (t : ℝ) := by exact_mod_cast ht
  have htReal1 : (t : ℝ) ≤ 1 := by exact_mod_cast htOne
  obtain ⟨n, hlo, hhi⟩ :=
    LevyStochCalc.Brownian.Continuity.exists_dyadic_scale_readable
      htReal0 htReal1
  have hloNN : ((1 : ℝ≥0) / 2) ^ (n + 1) < t := by
    exact_mod_cast hlo
  have hhiNN : t ≤ ((1 : ℝ≥0) / 2) ^ n := by
    exact_mod_cast hhi
  have hN : N ≤ n := by
    by_contra h
    have hnN : n + 1 ≤ N :=
      Nat.succ_le_iff.mpr (Nat.lt_of_not_ge h)
    have hContradict :
        ((1 : ℝ≥0) / 2) ^ N ≤ t :=
      (hAnti hnN).trans (le_of_lt hloNN)
    exact (not_le_of_gt htN) hContradict
  exact ⟨n, hN, le_of_lt hloNN, hhiNN⟩

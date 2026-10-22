-- Prove2me | solution 1 for GDGen3.M_le_h
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:32:05.181931+00:00
-- url     : https://prove2.me/submissions/44e62624-d739-4c49-91c2-d591f6f17c4c

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_M_le_h

lemma pj_step (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    r ^ 2 * pj r (i + 1) - pj r i = (1 - r ^ 2) / 2 := by
  simp only [pj, Nat.mul_add, pow_add]
  field_simp
  ring

lemma PiS_closed (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) :
    PiS r i = pj r i / (1 - r ^ 2) - (i : ℝ) / 2 := by
  have hr2 : r ^ 2 < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  have hne : 1 - r ^ 2 ≠ 0 := by linarith
  induction i with
  | zero => simp [PiS, pj]
  | succ i ih =>
    have hp := pj_step r (ne_of_gt hr) i
    change PiS r (i + 1) = _
    rw [PiS, sum_range_succ]
    change PiS r i + pj r (i + 1) = _
    rw [ih]
    push_cast
    field_simp [hne]
    nlinarith [hp]

lemma M_gap (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    (1 + r) - M r N =
      ((1 + (N : ℝ) * (1 + r)) ^ 2 - 1 / r ^ (2 * N)) /
        ((1 + r) * (N : ℝ) * ((N : ℝ) + 1)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hr2 : 1 - r ^ 2 ≠ 0 := by
    have ht : r ^ 2 < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
    linarith
  unfold M
  rw [PiS_closed r hr hr1 N]
  unfold pj
  field_simp
  ring

end GDGen3Proof_M_le_h

open GDGen3Proof_M_le_h

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) : M r N ≤ 1 + r := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hb : (1 / r ^ N) ^ 2 ≤ (1 + (N : ℝ) * (1 + r)) ^ 2 := by
    have hi : 0 ≤ 1 / r ^ N := by positivity
    nlinarith
  have he : (1 / r ^ N) ^ 2 = 1 / r ^ (2 * N) := by
    rw [Nat.mul_comm 2 N, pow_mul, div_pow, one_pow]
  rw [he] at hb
  have hgap : 0 ≤ (1 + r) - M r N := by
    rw [M_gap r hr hr1 N hN]
    apply div_nonneg (by linarith) (by positivity)
  linarith

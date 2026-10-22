-- Prove2me | solution 1 for GDGen3.M_gap
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:31:46.06199+00:00
-- url     : https://prove2.me/submissions/f29221d5-ff9d-4cf1-87b9-7cc2bce28b75

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_M_gap

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

end GDGen3Proof_M_gap

open GDGen3Proof_M_gap

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
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

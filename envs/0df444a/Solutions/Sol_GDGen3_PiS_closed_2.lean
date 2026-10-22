-- Prove2me | solution 2 for GDGen3.PiS_closed
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:27:46.583419+00:00
-- url     : https://prove2.me/submissions/4b034e04-ca6c-49ed-ba9c-d288b873762e

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_PiS_closed

lemma pj_step (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    r ^ 2 * pj r (i + 1) - pj r i = (1 - r ^ 2) / 2 := by
  simp only [pj, Nat.mul_add, pow_add]
  field_simp
  ring

end GDGen3Proof_PiS_closed

open GDGen3Proof_PiS_closed

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) :
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

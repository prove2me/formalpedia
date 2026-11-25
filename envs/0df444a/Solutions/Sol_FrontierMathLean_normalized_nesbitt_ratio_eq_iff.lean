-- Prove2me | solution 1 for FrontierMathLean.normalized_nesbitt_ratio_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:50:51.239005+00:00
-- url     : https://prove2.me/submissions/10d0d9ee-6563-4c4e-9eba-f4814f0ae2cb

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_FrontierMathLean_NesbittRatioInequality
import Theorems.Thm_FrontierMathLean_balanced_pair_fraction_le
import Theorems.Thm_FrontierMathLean_nesbitt_envelope_strict

set_option autoImplicit false
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution
    {x y r : ℝ} (hr : 1 < r) (hrx : r ≤ x) (hry : r ≤ y) :
    1 / (x + y) + x / (1 + y) + y / (1 + x) =
        (4 * r ^ 2 + r + 1) / (2 * (r ^ 2 + r)) ↔
      x = r ∧ y = r := by
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hxpos : 0 < x := lt_of_lt_of_le hrpos hrx
  have hypos : 0 < y := lt_of_lt_of_le hrpos hry
  have htwor : 2 < 2 * r := by linarith
  have hsum : 2 * r ≤ x + y := by linarith
  have hnormalized :
      (4 * r ^ 2 + r + 1) / (2 * (r ^ 2 + r)) =
        1 / (2 * r) + 2 * (2 * r) / (2 * r + 2) := by
    field_simp [hrpos.ne']
    ring
  constructor
  · intro hEq
    have hbalance := balanced_pair_fraction_le hxpos hypos
    have hsum_eq : x + y = 2 * r := by
      apply le_antisymm
      · by_contra hnot
        have hstrict_sum : 2 * r < x + y := lt_of_not_ge hnot
        have hstrict := nesbitt_envelope_strict htwor hstrict_sum
        rw [← hnormalized] at hstrict
        linarith
      · exact hsum
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    field_simp [hrpos.ne']
    ring
end FrontierMathLean

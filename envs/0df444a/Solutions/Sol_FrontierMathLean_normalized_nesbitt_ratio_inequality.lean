-- Prove2me | solution 1 for FrontierMathLean.normalized_nesbitt_ratio_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:47:33.04394+00:00
-- url     : https://prove2.me/submissions/39716c5a-1b12-4e33-8ba5-567989d02818

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_FrontierMathLean_NesbittRatioInequality
import Theorems.Thm_FrontierMathLean_balanced_pair_fraction_le
import Theorems.Thm_FrontierMathLean_nesbitt_envelope_mono

set_option autoImplicit false
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution
    {x y r : ℝ} (hr : 1 ≤ r) (hrx : r ≤ x) (hry : r ≤ y) :
    (4 * r ^ 2 + r + 1) / (2 * (r ^ 2 + r)) ≤
      1 / (x + y) + x / (1 + y) + y / (1 + x) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hxpos : 0 < x := lt_of_lt_of_le hrpos hrx
  have hypos : 0 < y := lt_of_lt_of_le hrpos hry
  have htwor : 2 ≤ 2 * r := by linarith
  have hsum : 2 * r ≤ x + y := by linarith
  have hmono := nesbitt_envelope_mono htwor hsum
  have hbalance := balanced_pair_fraction_le hxpos hypos
  have hnormalized :
      (4 * r ^ 2 + r + 1) / (2 * (r ^ 2 + r)) =
        1 / (2 * r) + 2 * (2 * r) / (2 * r + 2) := by
    field_simp [hrpos.ne']
    ring
  rw [hnormalized]
  linarith
end FrontierMathLean

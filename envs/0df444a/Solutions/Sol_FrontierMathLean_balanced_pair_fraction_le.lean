-- Prove2me | solution 1 for FrontierMathLean.balanced_pair_fraction_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:36:44.966256+00:00
-- url     : https://prove2.me/submissions/3eb26bdf-8eab-4026-b6eb-3e6c47e5cf9c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_FrontierMathLean_NesbittRatioInequality

set_option autoImplicit false
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    2 * (x + y) / (x + y + 2) ≤ x / (1 + y) + y / (1 + x) := by
  have hxy2 : 0 < x + y + 2 := by linarith
  have h1x : 0 < 1 + x := by linarith
  have h1y : 0 < 1 + y := by linarith
  have hden : 0 < (1 + x) * (1 + y) * (x + y + 2) := by positivity
  have hid :
      x / (1 + y) + y / (1 + x) - 2 * (x + y) / (x + y + 2) =
        ((x + y + 1) * (x - y) ^ 2) /
          ((1 + x) * (1 + y) * (x + y + 2)) := by
    field_simp [h1x.ne', h1y.ne', hxy2.ne']
    ring
  rw [← sub_nonneg, hid]
  positivity
end FrontierMathLean

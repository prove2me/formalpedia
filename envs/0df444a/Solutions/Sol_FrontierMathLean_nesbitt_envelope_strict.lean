-- Prove2me | solution 1 for FrontierMathLean.nesbitt_envelope_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:36:53.463742+00:00
-- url     : https://prove2.me/submissions/bc0c47ff-d667-4a74-8b10-036d37f79e55

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_FrontierMathLean_NesbittRatioInequality

set_option autoImplicit false
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution
    {s t : ℝ} (ht : 2 < t) (hts : t < s) :
    1 / t + 2 * t / (t + 2) < 1 / s + 2 * s / (s + 2) := by
  have htpos : 0 < t := by linarith
  have hspos : 0 < s := lt_trans htpos hts
  have ht2 : 0 < t + 2 := by linarith
  have hs2 : 0 < s + 2 := by linarith
  have hfactor : 0 < 3 * s * t - 2 * s - 2 * t - 4 := by
    have hst : 0 < (s - 2) * (t - 2) :=
      mul_pos (sub_pos.mpr (lt_trans ht hts)) (sub_pos.mpr ht)
    nlinarith
  have hid :
      (1 / s + 2 * s / (s + 2)) - (1 / t + 2 * t / (t + 2)) =
        ((s - t) * (3 * s * t - 2 * s - 2 * t - 4)) /
          (s * t * (s + 2) * (t + 2)) := by
    field_simp [hspos.ne', htpos.ne', hs2.ne', ht2.ne']
    ring
  rw [← sub_pos, hid]
  positivity
end FrontierMathLean

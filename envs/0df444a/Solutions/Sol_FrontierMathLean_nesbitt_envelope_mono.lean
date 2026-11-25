-- Prove2me | solution 1 for FrontierMathLean.nesbitt_envelope_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:36:51.391178+00:00
-- url     : https://prove2.me/submissions/0106a084-b377-40f9-8a99-4038579d21f2

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_FrontierMathLean_NesbittRatioInequality

set_option autoImplicit false
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution
    {s t : ℝ} (ht : 2 ≤ t) (hts : t ≤ s) :
    1 / t + 2 * t / (t + 2) ≤ 1 / s + 2 * s / (s + 2) := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hspos : 0 < s := lt_of_lt_of_le htpos hts
  have ht2 : 0 < t + 2 := by linarith
  have hs2 : 0 < s + 2 := by linarith
  have hfactor : 0 ≤ 3 * s * t - 2 * s - 2 * t - 4 := by
    have hst : 0 ≤ (s - 2) * (t - 2) :=
      mul_nonneg (sub_nonneg.mpr (ht.trans hts)) (sub_nonneg.mpr ht)
    nlinarith
  have hid :
      (1 / s + 2 * s / (s + 2)) - (1 / t + 2 * t / (t + 2)) =
        ((s - t) * (3 * s * t - 2 * s - 2 * t - 4)) /
          (s * t * (s + 2) * (t + 2)) := by
    field_simp [hspos.ne', htpos.ne', hs2.ne', ht2.ne']
    ring
  rw [← sub_nonneg, hid]
  positivity
end FrontierMathLean

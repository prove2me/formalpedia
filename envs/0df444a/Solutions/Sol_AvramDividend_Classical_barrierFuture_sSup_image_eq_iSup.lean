-- Prove2me | solution 1 for AvramDividend.Classical.barrierFuture_sSup_image_eq_iSup
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:13:06.133533+00:00
-- url     : https://prove2.me/submissions/bcb41b21-56b8-4c62-9ec2-f28140b9a0d9

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (f : ℝ≥0 → ℝ) (t : ℝ≥0)
    (hbound : BddAbove (f '' Icc (0 : ℝ≥0) t)) :
    sSup (f '' Icc (0 : ℝ≥0) t) =
      ⨆ s : Icc (0 : ℝ≥0) t, f s.1 := by
  rw [sSup_image']

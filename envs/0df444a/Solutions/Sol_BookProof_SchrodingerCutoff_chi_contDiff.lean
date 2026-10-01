-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.chi_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T09:09:23.590217+00:00
-- url     : https://prove2.me/submissions/f2c6082a-87c9-4167-b598-6b1f4e9a5921

import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa

open BookProof.SchrodingerCutoff

theorem solution : ContDiff ℝ 2 chi := by
  change ContDiff ℝ 2 (⇑bump0)
  exact ContDiffBump.contDiff (n := 2) bump0

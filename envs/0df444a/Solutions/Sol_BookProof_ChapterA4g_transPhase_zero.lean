-- Prove2me | solution 1 for BookProof.ChapterA4g.transPhase_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T04:29:51.904394+00:00
-- url     : https://prove2.me/submissions/05cf10cb-569f-4371-bd9b-33ce45273a6e

import Definitions.Def_ChapterA4g
import Mathlib

open BookProof.ChapterA4g Complex

theorem solution (p : Fin 3 → ℝ) : transPhase p 0 = 1 := by
  simp [transPhase, Pi.zero_apply, mul_zero, Finset.sum_const_zero, exp_zero]

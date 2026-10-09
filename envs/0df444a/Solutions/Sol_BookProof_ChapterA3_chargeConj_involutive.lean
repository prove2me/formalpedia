-- Prove2me | solution 1 for BookProof.ChapterA3.chargeConj_involutive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:03:37.48277+00:00
-- url     : https://prove2.me/submissions/602042a9-7682-4a62-8dba-212acae6db8c

-- Generated from ChapterA3b.lean — solution of BookProof.ChapterA3.chargeConj_involutive
import Mathlib
import Definitions.Def_ChapterA3b
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution : Function.Involutive chargeConj := by

  intro v; funext i; simp [chargeConj]

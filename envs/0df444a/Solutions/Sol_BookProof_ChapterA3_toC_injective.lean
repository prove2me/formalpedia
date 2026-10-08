-- Prove2me | solution 1 for BookProof.ChapterA3.toC_injective
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:05:20.293558+00:00
-- url     : https://prove2.me/submissions/8275ccac-4936-4a4c-b14b-97f0df1f1c0e

import Mathlib
import Definitions.Def_ChapterA3b
open BookProof.ChapterA3 Matrix

theorem solution : Function.Injective toC := by
  intro M N h
  ext i j
  exact Complex.ofReal_injective (congrArg (fun A => A i j) h)

#print axioms solution

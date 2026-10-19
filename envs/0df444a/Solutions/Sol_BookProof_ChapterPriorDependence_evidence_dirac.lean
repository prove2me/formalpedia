-- Prove2me | solution 1 for BookProof.ChapterPriorDependence.evidence_dirac
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:39:32.439815+00:00
-- url     : https://prove2.me/submissions/189543c9-9274-42c6-a6dd-85c4a1f7de92

import Mathlib
import Definitions.Def_ChapterPriorDependence
import Definitions.Def_ChapterBayesInference
-- Generated from ChapterPriorDependence.lean — theorem BookProof.ChapterPriorDependence.evidence_dirac
open BookProof.ChapterBayesInference
open BookProof.ChapterPriorDependence


open scoped BigOperators


variable {Hyp Data : Type*} [DecidableEq Hyp]

variable [Fintype Hyp]


theorem solution (a : Hyp) (L : Hyp → Data → ℝ) (d : Data) :
    BookProof.ChapterBayesInference.evidence (diracPrior a) L d = L a d := by
  simp [BookProof.ChapterBayesInference.evidence, diracPrior]


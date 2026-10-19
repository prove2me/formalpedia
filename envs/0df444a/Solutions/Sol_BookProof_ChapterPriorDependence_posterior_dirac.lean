-- Prove2me | solution 1 for BookProof.ChapterPriorDependence.posterior_dirac
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:39:41.477858+00:00
-- url     : https://prove2.me/submissions/354c7706-4ae8-40cc-93b2-644df42c9e6d

import Mathlib
import Definitions.Def_ChapterPriorDependence
import Definitions.Def_ChapterBayesInference
-- Generated from ChapterPriorDependence.lean — theorem BookProof.ChapterPriorDependence.posterior_dirac
open BookProof.ChapterBayesInference
open BookProof.ChapterPriorDependence


open scoped BigOperators


variable {Hyp Data : Type*} [DecidableEq Hyp]

variable [Fintype Hyp]


theorem solution (a : Hyp) (L : Hyp → Data → ℝ) (d : Data)
    (ha : 0 < L a d) (x : Hyp) :
    BookProof.ChapterBayesInference.posterior (diracPrior a) L d x =
      diracPrior a x := by
  have he : BookProof.ChapterBayesInference.evidence (diracPrior a) L d = L a d := by
    simp [BookProof.ChapterBayesInference.evidence, diracPrior]
  unfold BookProof.ChapterBayesInference.posterior
  rw [he]
  by_cases hx : x = a
  · subst hx; simp [diracPrior, ha.ne']
  · simp [diracPrior, hx]


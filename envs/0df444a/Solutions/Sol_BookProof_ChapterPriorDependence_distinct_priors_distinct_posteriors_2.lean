-- Prove2me | solution 2 for BookProof.ChapterPriorDependence.distinct_priors_distinct_posteriors
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:39:48.565851+00:00
-- url     : https://prove2.me/submissions/3c82231f-380f-4c19-a918-7c1677970005

import Mathlib
import Definitions.Def_ChapterPriorDependence
import Definitions.Def_ChapterBayesInference
-- Generated from ChapterPriorDependence.lean — theorem BookProof.ChapterPriorDependence.distinct_priors_distinct_posteriors
open BookProof.ChapterBayesInference
open BookProof.ChapterPriorDependence


open scoped BigOperators


variable {Hyp Data : Type*} [DecidableEq Hyp]

variable [Fintype Hyp]


theorem solution (a b : Hyp) (hab : a ≠ b)
    (L : Hyp → Data → ℝ) (d : Data) (ha : 0 < L a d) :
    BookProof.ChapterBayesInference.posterior (diracPrior a) L d ≠
      BookProof.ChapterBayesInference.posterior (diracPrior b) L d := by
  intro h
  have h1 := congrFun h a
  have hea : BookProof.ChapterBayesInference.evidence (diracPrior a) L d = L a d := by
    simp [BookProof.ChapterBayesInference.evidence, diracPrior]
  unfold BookProof.ChapterBayesInference.posterior at h1
  rw [hea] at h1
  simp [diracPrior, hab, ha.ne'] at h1


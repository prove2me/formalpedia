-- Prove2me | solution 1 for BookProof.ChapterPriorDependence.distinct_priors_distinct_posteriors
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:55.528741+00:00
-- url     : https://prove2.me/submissions/f2252d7a-97c0-4fe3-92d6-9c1e8f5505f2

-- Generated from ChapterPriorDependence.lean — solution of BookProof.ChapterPriorDependence.distinct_priors_distinct_posteriors
import Mathlib
import Definitions.Def_ChapterPriorDependence
import Theorems.Thm_BookProof_ChapterPriorDependence_posterior_dirac
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterPriorDependence



open scoped BigOperators


variable {Hyp Data : Type*} [DecidableEq Hyp]

variable {Hyp Data : Type*} [DecidableEq Hyp]
variable [Fintype Hyp]

set_option maxHeartbeats 1000000 in
theorem solution (a b : Hyp) (hab : a ≠ b)
    (L : Hyp → Data → ℝ) (d : Data) (ha : 0 < L a d) :
    BookProof.ChapterBayesInference.posterior (diracPrior a) L d ≠
      BookProof.ChapterBayesInference.posterior (diracPrior b) L d := by

  intro h
  have heq := congrFun h a
  rw [posterior_dirac a L d ha a] at heq
  simp [diracPrior, hab, BookProof.ChapterBayesInference.posterior] at heq

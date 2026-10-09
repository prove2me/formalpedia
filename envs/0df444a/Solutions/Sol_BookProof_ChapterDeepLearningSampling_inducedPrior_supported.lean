-- Prove2me | solution 1 for BookProof.ChapterDeepLearningSampling.inducedPrior_supported
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:49:11.103168+00:00
-- url     : https://prove2.me/submissions/35981eef-f50f-43dd-958b-9fd0f38bccc3

-- Generated from ChapterDeepLearningSampling.lean — solution of BookProof.ChapterDeepLearningSampling.inducedPrior_supported
import Mathlib
import Definitions.Def_ChapterDeepLearningSampling
open BookProof.ChapterDeepLearningSampling



open scoped BigOperators


variable {Seed Model Data : Type*}
variable [Fintype Seed] [DecidableEq Model]

variable {Seed Model Data : Type*}
variable [Fintype Seed] [DecidableEq Model]

set_option maxHeartbeats 1000000 in
theorem solution (seedProb : Seed → ℝ) (train : Seed → Model)
    (admissible : Model → Prop)
    (htrain : ∀ s, admissible (train s)) {m : Model} (hm : ¬ admissible m) :
    inducedPrior seedProb train m = 0 := by

  exact Finset.sum_eq_zero fun s hs => False.elim <| hm <| by aesop

-- Prove2me | solution 1 for BookProof.ChapterBijectionProbability.bijProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:28:21.205054+00:00
-- url     : https://prove2.me/submissions/54750bb5-5e8c-4f81-960e-2171f79f56b7

-- Generated from ChapterBijectionProbability.lean — solution of BookProof.ChapterBijectionProbability.bijProb_nonneg
import Mathlib
import Definitions.Def_ChapterBijectionProbability
open BookProof.ChapterBijectionProbability



open scoped Nat
open Filter Asymptotics

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) : 0 ≤ bijProb n := by

  unfold bijProb; positivity

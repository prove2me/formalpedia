-- Prove2me | solution 2 for BookProof.ChapterSirkEndToEnd.crouzeix_domain_uniform
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T11:26:19.590269+00:00
-- url     : https://prove2.me/submissions/f889c059-d8d7-4600-94d6-e886f0cd717a

-- Generated from ChapterSirkEndToEnd.lean — solution of BookProof.ChapterSirkEndToEnd.crouzeix_domain_uniform
import Mathlib
import Definitions.Def_ChapterSirkEndToEnd
import Theorems.Thm_BookProof_ChapterSirkEndToEnd_crouzeix_domain_transfer
import Theorems.Thm_BookProof_ChapterH9_numRange_subset_closedBall
open BookProof.ChapterSirkEndToEnd











noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) :
    (convexHull ℝ) (numRange (compress V X)) ⊆ Metric.closedBall (0 : ℂ) ‖X‖ :=
  crouzeix_domain_transfer V X hViso _ (convex_closedBall _ _)
      (numRange_subset_closedBall X)

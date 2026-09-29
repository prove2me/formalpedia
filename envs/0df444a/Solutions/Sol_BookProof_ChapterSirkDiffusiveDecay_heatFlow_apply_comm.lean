-- Prove2me | solution 1 for BookProof.ChapterSirkDiffusiveDecay.heatFlow_apply_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-09T12:09:56.503074+00:00
-- url     : https://prove2.me/submissions/84bff762-ffd9-4752-986a-ef8c199228e7

-- Generated from ChapterSirkDiffusiveDecay.lean — solution of BookProof.ChapterSirkDiffusiveDecay.heatFlow_apply_comm
import Mathlib
import Definitions.Def_ChapterSirkDiffusiveDecay
open BookProof.ChapterSirkDiffusiveDecay










noncomputable section


open BookProof.ChapterH4
open Filter Topology NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (A : E →L[ℂ] E) (t : ℝ) (v : E) :
    heatFlow A t (A v) = A (heatFlow A t v) := by

  have hcomm : exp ((-t) • A) * A = A * exp ((-t) • A) :=
    (((Commute.refl A).smul_right (-t)).exp_right.eq).symm
  have := congrArg (fun T : E →L[ℂ] E => T v) hcomm
  simpa [heatFlow, ContinuousLinearMap.mul_apply] using this

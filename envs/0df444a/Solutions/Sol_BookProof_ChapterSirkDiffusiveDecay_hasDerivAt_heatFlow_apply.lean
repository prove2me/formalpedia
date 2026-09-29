-- Prove2me | solution 1 for BookProof.ChapterSirkDiffusiveDecay.hasDerivAt_heatFlow_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-09T12:19:54.393004+00:00
-- url     : https://prove2.me/submissions/94e1d980-015f-47e8-a51f-691ee562fa9d

-- Generated from ChapterSirkDiffusiveDecay.lean — solution of BookProof.ChapterSirkDiffusiveDecay.hasDerivAt_heatFlow_apply
import Mathlib
import Definitions.Def_ChapterSirkDiffusiveDecay
import Theorems.Thm_BookProof_ChapterSirkDiffusiveDecay_heatFlow_apply_comm
open BookProof.ChapterSirkDiffusiveDecay










noncomputable section


open BookProof.ChapterH4
open Filter Topology NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (A : E →L[ℂ] E) (v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => heatFlow A s v) (-(A (heatFlow A t v))) t := by

  have h0 := hasDerivAt_exp_smul_const (𝕂 := ℝ) A (-t)
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := (hasDerivAt_id t).neg
  have h : HasDerivAt (fun s : ℝ => exp ((-s) • A)) (-(exp ((-t) • A) * A)) t := by
    simpa [Function.comp_def] using h0.scomp t hneg
  have h2 := ((ContinuousLinearMap.apply ℂ E v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h
  rw [← heatFlow_apply_comm A t v]
  simpa [heatFlow, Function.comp_def, ContinuousLinearMap.mul_apply] using h2

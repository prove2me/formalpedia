-- Prove2me | solution 1 for BookProof.ChapterF7.smul_l2Symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:08:38.189153+00:00
-- url     : https://prove2.me/submissions/9de3ddd9-0d81-4756-8fcd-caed61229ad4

-- Generated from ChapterF7.lean — solution of BookProof.ChapterF7.smul_l2Symmetric
import Mathlib
import Definitions.Def_ChapterF7
import Theorems.Thm_BookProof_ChapterF7_l2pair_smul_left
import Theorems.Thm_BookProof_ChapterF7_l2pair_smul_right
open BookProof.ChapterF7



open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {c : ℂ} (hc : (starRingEnd ℂ) c = c)
    {T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)} (hT : IsL2Symmetric T) :
    IsL2Symmetric (c • T) := by

  intro f g
  simp only [ContinuousLinearMap.smul_apply]
  rw [l2pair_smul_left, l2pair_smul_right, hc, hT]

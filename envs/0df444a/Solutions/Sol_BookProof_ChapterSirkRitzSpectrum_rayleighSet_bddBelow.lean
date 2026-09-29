-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.rayleighSet_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:48:37.265367+00:00
-- url     : https://prove2.me/submissions/89819228-47c9-45ba-bfb4-3959fe392f74

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.rayleighSet_bddBelow
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_neg_norm_le_re_inner
open BookProof.ChapterSirkRitzSpectrum








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (T : F →L[ℂ] F) : BddBelow (rayleighSet T) := by

  refine ⟨-‖T‖, ?_⟩
  rintro t ⟨x, hx1, rfl⟩
  have := neg_norm_le_re_inner T x
  rw [hx1] at this
  simpa using this

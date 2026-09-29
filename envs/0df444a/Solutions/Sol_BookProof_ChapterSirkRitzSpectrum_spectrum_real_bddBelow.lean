-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.spectrum_real_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:50:39.315593+00:00
-- url     : https://prove2.me/submissions/a4f5a19a-41a8-4298-9cd9-7fbae9690597

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.spectrum_real_bddBelow
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_le_rayleigh_iff_le_spectrum
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_neg_norm_le_re_inner
open BookProof.ChapterSirkRitzSpectrum








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) :
    BddBelow (spectrum ℝ T) := by

  refine ⟨-‖T‖, ?_⟩
  intro μ hμ
  refine (le_rayleigh_iff_le_spectrum T hT (-‖T‖)).mp ?_ μ hμ
  intro x
  have := neg_norm_le_re_inner T x
  linarith

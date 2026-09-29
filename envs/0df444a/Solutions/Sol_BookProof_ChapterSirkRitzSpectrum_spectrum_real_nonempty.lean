-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.spectrum_real_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:52:31.180446+00:00
-- url     : https://prove2.me/submissions/2a4eb47a-4aaf-4030-8565-9954b996d0e6

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.spectrum_real_nonempty
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_le_rayleigh_iff_le_spectrum
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_re_inner_le_norm
open BookProof.ChapterSirkRitzSpectrum








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial F] (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) :
    (spectrum ℝ T).Nonempty := by

  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  set x : F := ‖y‖⁻¹ • y with hx
  have hxnorm : ‖x‖ = 1 := by
    rw [hx, norm_smul]
    simp [norm_ne_zero_iff.mpr hy]
  have hbound := (le_rayleigh_iff_le_spectrum T hT (‖T‖ + 1)).mpr
    (by intro μ hμ; rw [hempty] at hμ; simp at hμ) x
  have hupper := re_inner_le_norm T x
  rw [hxnorm] at hbound hupper
  norm_num at hbound hupper
  linarith

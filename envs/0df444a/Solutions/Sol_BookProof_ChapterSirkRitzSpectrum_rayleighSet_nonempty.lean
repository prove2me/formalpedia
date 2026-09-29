-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.rayleighSet_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:58:02.909888+00:00
-- url     : https://prove2.me/submissions/3a8a8083-e148-4600-9b40-b1a95e1e2502

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.rayleighSet_nonempty
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial F] (T : F →L[ℂ] F) : (rayleighSet T).Nonempty := by

  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  refine ⟨_, ‖y‖⁻¹ • y, ?_, rfl⟩
  rw [norm_smul]
  simp [norm_ne_zero_iff.mpr hy]

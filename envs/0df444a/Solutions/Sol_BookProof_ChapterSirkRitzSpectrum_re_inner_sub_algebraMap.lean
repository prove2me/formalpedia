-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.re_inner_sub_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:02:23.142661+00:00
-- url     : https://prove2.me/submissions/da354d53-a8ea-4d75-8d6b-01c6ac845b9c

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.re_inner_sub_algebraMap
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (T : F →L[ℂ] F) (c : ℝ) (x : F) :
    (inner ℂ ((T - (algebraMap ℝ (F →L[ℂ] F)) c) x) x : ℂ).re
      = (inner ℂ (T x) x : ℂ).re - c * ‖x‖ ^ 2 := by

  have h : (T - (algebraMap ℝ (F →L[ℂ] F)) c) x = T x - (c : ℂ) • x := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [h, inner_sub_left, Complex.sub_re, inner_smul_left]
  simp [Complex.conj_ofReal, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

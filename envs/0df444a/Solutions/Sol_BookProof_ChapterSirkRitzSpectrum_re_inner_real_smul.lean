-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.re_inner_real_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:01:02.898022+00:00
-- url     : https://prove2.me/submissions/cf70a3f9-8f95-4330-8c5a-7d0488134668

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.re_inner_real_smul
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (T : F →L[ℂ] F) (c : ℝ) (x : F) :
    (inner ℂ ((c : ℂ) • x) (T ((c : ℂ) • x)) : ℂ).re = c ^ 2 * (inner ℂ x (T x) : ℂ).re := by

  rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right]
  simp [Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, sq]

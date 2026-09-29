-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.abs_re_inner_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:56:32.811866+00:00
-- url     : https://prove2.me/submissions/8967c459-21e9-482d-95e1-4ebe070af61f

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.abs_re_inner_le
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (T : F →L[ℂ] F) (x : F) :
    |(inner ℂ x (T x) : ℂ).re| ≤ ‖T‖ * ‖x‖ ^ 2 := by

  calc |(inner ℂ x (T x) : ℂ).re| ≤ ‖(inner ℂ x (T x) : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) := mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg _)
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring

-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.neg_norm_le_re_inner
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:38:25.003774+00:00
-- url     : https://prove2.me/submissions/9f38d9b4-1f33-4234-867f-5fdc085e5bc2

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.neg_norm_le_re_inner
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_abs_re_inner_le
open BookProof.ChapterSirkRitzSpectrum








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (T : F →L[ℂ] F) (x : F) :
    -(‖T‖ * ‖x‖ ^ 2) ≤ (inner ℂ x (T x) : ℂ).re := neg_le_of_abs_le (abs_re_inner_le T x)

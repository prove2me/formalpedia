-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.re_inner_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:39:57.049328+00:00
-- url     : https://prove2.me/submissions/008fe909-f8e7-4180-ac7f-1955ee649d12

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.re_inner_le_norm
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_abs_re_inner_le
open BookProof.ChapterSirkRitzSpectrum








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (T : F →L[ℂ] F) (x : F) :
    (inner ℂ x (T x) : ℂ).re ≤ ‖T‖ * ‖x‖ ^ 2 := (le_abs_self _).trans (abs_re_inner_le T x)

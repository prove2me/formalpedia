-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.selfAdjoint_re_inner_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:06:42.344545+00:00
-- url     : https://prove2.me/submissions/b899118c-9b07-450a-9eca-db53a9d7bfa5

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.selfAdjoint_re_inner_coe
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (x : F) :
    (((inner ℂ (T x) x : ℂ).re : ℝ) : ℂ) = inner ℂ (T x) x := by

  have hsym := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) x x
  refine Complex.conj_eq_iff_re.mp ?_
  rw [inner_conj_symm]
  exact hsym.symm

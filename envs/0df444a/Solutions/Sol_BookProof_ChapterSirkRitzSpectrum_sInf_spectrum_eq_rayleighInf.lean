-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.sInf_spectrum_eq_rayleighInf
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T08:05:48.958473+00:00
-- url     : https://prove2.me/submissions/76d3e9ef-da65-4028-8db9-b0850307bfa6

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.sInf_spectrum_eq_rayleighInf
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_le_rayleigh_iff_le_spectrum
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_spectrum_real_nonempty
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_spectrum_real_bddBelow
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_rayleighSet_nonempty
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_rayleighInf_mul_normSq_le
open BookProof.ChapterSirkRitzSpectrum








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial F] (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) :
    sInf (spectrum ℝ T) = rayleighInf T := by

  have hspecne := spectrum_real_nonempty T hT
  have hspecbdd := spectrum_real_bddBelow T hT
  refine le_antisymm ?_ ?_
  · -- every Rayleigh quotient dominates the bottom of the spectrum
    refine le_csInf (rayleighSet_nonempty T) ?_
    rintro t ⟨x, hx1, rfl⟩
    have hlb : ∀ μ ∈ spectrum ℝ T, sInf (spectrum ℝ T) ≤ μ := fun μ hμ => csInf_le hspecbdd hμ
    have := (le_rayleigh_iff_le_spectrum T hT (sInf (spectrum ℝ T))).mpr hlb x
    rwa [hx1, one_pow, mul_one] at this
  · -- and the bottom of the numerical range is a lower bound for the spectrum
    refine le_csInf hspecne ?_
    intro μ hμ
    exact (le_rayleigh_iff_le_spectrum T hT (rayleighInf T)).mp
      (rayleighInf_mul_normSq_le T) μ hμ

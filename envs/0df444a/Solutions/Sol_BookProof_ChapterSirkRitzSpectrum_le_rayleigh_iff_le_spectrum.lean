-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.le_rayleigh_iff_le_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:42:04.211609+00:00
-- url     : https://prove2.me/submissions/8a4e0fe1-7f0d-4370-a16d-ac219e3e2eae

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.le_rayleigh_iff_le_spectrum
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_selfAdjoint_re_inner_coe
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_re_inner_comm
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_re_inner_sub_algebraMap
open BookProof.ChapterSirkRitzSpectrum








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (c : ℝ) :
    (∀ x : F, c * ‖x‖ ^ 2 ≤ (inner ℂ x (T x) : ℂ).re) ↔ ∀ μ ∈ spectrum ℝ T, c ≤ μ := by

  have hS : IsSelfAdjoint (T - (algebraMap ℝ (F →L[ℂ] F)) c) :=
    hT.sub (IsSelfAdjoint.algebraMap (F →L[ℂ] F) rfl)
  have hmain := StarOrderedRing.nonneg_iff_spectrum_nonneg
    (R := ℝ) (T - (algebraMap ℝ (F →L[ℂ] F)) c) hS
  have hpos : (0 ≤ T - (algebraMap ℝ (F →L[ℂ] F)) c) ↔
      ∀ x : F, c * ‖x‖ ^ 2 ≤ (inner ℂ x (T x) : ℂ).re := by
    rw [nonneg_iff_isPositive, isPositive_iff_complex]
    constructor
    · intro h x
      have h2 := (h x).2
      rw [RCLike.re_to_complex, re_inner_sub_algebraMap T c x] at h2
      rw [← re_inner_comm]
      linarith
    · intro h x
      refine ⟨by simpa only [RCLike.re_to_complex] using selfAdjoint_re_inner_coe _ hS x, ?_⟩
      rw [RCLike.re_to_complex, re_inner_sub_algebraMap T c x, re_inner_comm]
      linarith [h x]
  have hspec : spectrum ℝ (T - (algebraMap ℝ (F →L[ℂ] F)) c) = spectrum ℝ T - {c} :=
    (spectrum.sub_singleton_eq T c).symm
  rw [← hpos, hmain]
  constructor
  · intro h μ hμ
    have := h (μ - c) (by rw [hspec]; exact ⟨μ, hμ, c, rfl, rfl⟩)
    linarith
  · intro h ν hν
    rw [hspec] at hν
    obtain ⟨μ, hμ, d, hd, rfl⟩ := hν
    simp only [Set.mem_singleton_iff] at hd
    subst hd
    linarith [h μ hμ]

-- Prove2me | solution 1 for BookProof.ChapterH9.exists_unit_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:40:20.29886+00:00
-- url     : https://prove2.me/submissions/e485dc13-a470-42fc-8986-3518e6978538

-- Generated from ChapterH9.lean — solution of BookProof.ChapterH9.exists_unit_eigenvector
import Mathlib
import Definitions.Def_ChapterH9
open BookProof.ChapterH9



noncomputable section


open BookProof.ChapterH1 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH8
open ContinuousLinearMap


variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

set_option maxHeartbeats 1000000 in
omit [CompleteSpace E] [CompleteSpace F] in
theorem solution [FiniteDimensional ℂ F] (A : F →L[ℂ] F) {lam : ℂ}
    (hlam : lam ∈ spectrum ℂ (A : F →ₗ[ℂ] F)) : ∃ y : F, ‖y‖ = 1 ∧ A y = lam • y := by

  obtain ⟨v, hmem, hv0⟩ :=
    (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hlam).exists_hasEigenvector
  have hAv : A v = lam • v := by
    simp only [Module.End.mem_genEigenspace_one, ContinuousLinearMap.coe_coe] at hmem
    exact hmem
  have hnv : (‖v‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hv0
  refine ⟨((‖v‖ : ℂ))⁻¹ • v, ?_, ?_⟩
  · rw [norm_smul]
    simp [hnv]
  · rw [map_smul, hAv, smul_comm]

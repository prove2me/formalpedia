-- Prove2me | solution 1 for BookProof.ChapterH9.spectrum_compress_subset_numRange
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:44:34.743916+00:00
-- url     : https://prove2.me/submissions/95b9563c-d4ae-45f5-83ae-51222ab98546

-- Generated from ChapterH9.lean — solution of BookProof.ChapterH9.spectrum_compress_subset_numRange
import Mathlib
import Definitions.Def_ChapterH9
import Theorems.Thm_BookProof_ChapterH9_ritz_mem_numRange
import Theorems.Thm_BookProof_ChapterH9_exists_unit_eigenvector
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
theorem solution [FiniteDimensional ℂ F] (V : F →L[ℂ] E)
    (X : E →L[ℂ] E) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) :
    spectrum ℂ ((compress V X : F →ₗ[ℂ] F)) ⊆ numRange X := by

  intro lam hlam
  obtain ⟨y, hy, heig⟩ := exists_unit_eigenvector (compress V X) hlam
  exact ritz_mem_numRange V X hViso hy heig

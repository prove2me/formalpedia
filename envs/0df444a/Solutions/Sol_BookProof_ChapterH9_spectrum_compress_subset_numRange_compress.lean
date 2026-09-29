-- Prove2me | solution 1 for BookProof.ChapterH9.spectrum_compress_subset_numRange_compress
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:47:20.191474+00:00
-- url     : https://prove2.me/submissions/675b7c65-4985-4122-b547-6ecb352418b5

-- Generated from ChapterH9.lean — solution of BookProof.ChapterH9.spectrum_compress_subset_numRange_compress
import Mathlib
import Definitions.Def_ChapterH9
import Theorems.Thm_BookProof_ChapterH9_ritz_mem_numRange_compress
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
theorem solution [FiniteDimensional ℂ F]
    (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G) (X : E →L[ℂ] E)
    (hJ : Vn = Vm.comp J) (hJiso : ∀ x : F, ‖J x‖ = ‖x‖) :
    spectrum ℂ ((compress Vn X : F →ₗ[ℂ] F)) ⊆ numRange (compress Vm X) := by

  intro lam hlam
  obtain ⟨y, hy, heig⟩ := exists_unit_eigenvector (compress Vn X) hlam
  exact ritz_mem_numRange_compress Vn Vm J X hJ hJiso hy heig

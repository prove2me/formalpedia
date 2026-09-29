-- Prove2me | solution 1 for BookProof.ChapterSirkGramWhitening.range_whitened
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:26.542555+00:00
-- url     : https://prove2.me/submissions/2685258d-c30f-4e7f-a259-3e36ef8ba595

-- Generated from ChapterSirkGramWhitening.lean — solution of BookProof.ChapterSirkGramWhitening.range_whitened
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
import Theorems.Thm_BookProof_ChapterSirkGramWhitening_range_synthesis
import Theorems.Thm_BookProof_ChapterSirkGramWhitening_range_whitened_le
open BookProof.ChapterSirkGramWhitening









noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} (w : Fin m → E)
    {T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)}
    (hT : Function.Surjective T) :
    LinearMap.range (whitened w T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E)
      = Submodule.span ℂ (Set.range w) := by

  refine le_antisymm (range_whitened_le w T) ?_
  rw [← range_synthesis w]
  rintro x ⟨c, rfl⟩
  obtain ⟨d, rfl⟩ := hT c
  exact ⟨d, rfl⟩

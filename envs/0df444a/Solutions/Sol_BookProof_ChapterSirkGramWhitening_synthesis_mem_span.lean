-- Prove2me | solution 1 for BookProof.ChapterSirkGramWhitening.synthesis_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:33:12.529719+00:00
-- url     : https://prove2.me/submissions/843a0d36-b0a1-48f7-b102-4109195ad5aa

-- Generated from ChapterSirkGramWhitening.lean — solution of BookProof.ChapterSirkGramWhitening.synthesis_mem_span
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
import Theorems.Thm_BookProof_ChapterSirkGramWhitening_range_synthesis
open BookProof.ChapterSirkGramWhitening









noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} (w : Fin m → E) (c : EuclideanSpace ℂ (Fin m)) :
    synthesis w c ∈ Submodule.span ℂ (Set.range w) := by

  rw [← range_synthesis w]; exact ⟨c, rfl⟩

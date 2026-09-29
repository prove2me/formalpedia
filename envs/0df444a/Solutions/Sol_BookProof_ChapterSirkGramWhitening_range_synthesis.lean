-- Prove2me | solution 1 for BookProof.ChapterSirkGramWhitening.range_synthesis
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:39:00.260635+00:00
-- url     : https://prove2.me/submissions/a8c68546-34b8-4d24-bc46-1bdca4a28335

-- Generated from ChapterSirkGramWhitening.lean — solution of BookProof.ChapterSirkGramWhitening.range_synthesis
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening









noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} (w : Fin m → E) :
    LinearMap.range (synthesis w : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E)
      = Submodule.span ℂ (Set.range w) := by

  ext x
  simp only [LinearMap.mem_range, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨fun i => c i, rfl⟩
  · rintro ⟨c, rfl⟩; exact ⟨WithLp.toLp 2 c, rfl⟩

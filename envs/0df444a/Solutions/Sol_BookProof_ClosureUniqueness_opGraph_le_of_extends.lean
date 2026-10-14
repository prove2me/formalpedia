-- Prove2me | solution 1 for BookProof.ClosureUniqueness.opGraph_le_of_extends
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:36.720454+00:00
-- url     : https://prove2.me/submissions/af399a53-4f9f-47df-a84f-5f4369ba3672

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.opGraph_le_of_extends
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (h : Extends T A) :
    opGraph T ≤ opGraph A := by

  rintro p ⟨v, rfl⟩
  obtain ⟨hv, hval⟩ := h v
  exact ⟨⟨(v : F), hv⟩, by simp [hval]⟩

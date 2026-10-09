-- Prove2me | solution 1 for BookProof.ClosureUniqueness.mem_adjGraph_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T09:47:59.298798+00:00
-- url     : https://prove2.me/submissions/c198b126-28b5-4fa7-abb9-1ded26f90e1d

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.mem_adjGraph_iff
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {T : D →ₗ[ℂ] F} {p : F × F} :
    p ∈ adjGraph T ↔ ∀ v : D, (inner ℂ (T v) p.1 : ℂ) = inner ℂ (v : F) p.2 := by

  constructor
  · intro h v; exact h _ (mem_opGraph T v)
  · rintro h q ⟨v, rfl⟩; exact h v

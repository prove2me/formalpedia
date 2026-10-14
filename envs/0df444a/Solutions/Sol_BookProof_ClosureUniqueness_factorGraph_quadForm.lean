-- Prove2me | solution 1 for BookProof.ClosureUniqueness.factorGraph_quadForm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:50.568974+00:00
-- url     : https://prove2.me/submissions/63254a85-ce67-4c6c-8332-f10f90b42beb

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.factorGraph_quadForm
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Theorems.Thm_BookProof_ClosureUniqueness_adjGraph_eq_adjPairs_clGraph
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorGraph A) :
    ∃ y : F, (p.1, y) ∈ clGraph A ∧ (inner ℂ p.1 p.2 : ℂ) = ((‖y‖ ^ 2 : ℝ) : ℂ) := by

  obtain ⟨y, hy, hz⟩ := hp
  rw [adjGraph_eq_adjPairs_clGraph] at hz
  refine ⟨y, hy, ?_⟩
  have h1 : (inner ℂ y y : ℂ) = inner ℂ p.1 p.2 := hz (p.1, y) hy
  rw [← h1, inner_self_eq_norm_sq_to_K]
  norm_cast

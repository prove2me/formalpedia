-- Prove2me | solution 1 for BookProof.ClosureUniqueness.factorGraph_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:49.394995+00:00
-- url     : https://prove2.me/submissions/51f59621-b82e-404b-8424-0901ded77717

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.factorGraph_symmetric
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
theorem solution {A : D →ₗ[ℂ] F} {p q : F × F} (hp : p ∈ factorGraph A)
    (hq : q ∈ factorGraph A) : (inner ℂ p.2 q.1 : ℂ) = inner ℂ p.1 q.2 := by

  obtain ⟨y, hy, hz⟩ := hp
  obtain ⟨y', hy', hz'⟩ := hq
  rw [adjGraph_eq_adjPairs_clGraph] at hz hz'
  have h1 : (inner ℂ y' y : ℂ) = inner ℂ q.1 p.2 := hz (q.1, y') hy'
  have h2 : (inner ℂ y y' : ℂ) = inner ℂ p.1 q.2 := hz' (p.1, y) hy
  have h3 : (inner ℂ p.2 q.1 : ℂ) = starRingEnd ℂ (inner ℂ q.1 p.2) :=
    (inner_conj_symm _ _).symm
  rw [h3, ← h1, inner_conj_symm]
  exact h2

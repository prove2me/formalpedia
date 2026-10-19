-- Prove2me | solution 1 for BookProof.ChapterSchurFiniteDim.schur_scalar_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:25:23.597058+00:00
-- url     : https://prove2.me/submissions/f46540be-33de-4c78-8cc9-0343cb3b817d

-- Generated from ChapterSchurFiniteDim.lean — solution of BookProof.ChapterSchurFiniteDim.schur_scalar_of_irreducible
import Mathlib
import Definitions.Def_ChapterSchurFiniteDim
import Definitions.Def_ChapterA
open BookProof.ChapterSchurFiniteDim



open Module


open BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution [FiniteDimensional ℂ V] [Nontrivial V]
    (M : System ℂ V) (hirr : IsIrreducibleSystem M) (f : V →ₗ[ℂ] V)
    (hf : ∀ m ∈ M.ops, ∀ x, f (m x) = m (f x)) :
    ∃ c : ℂ, ∀ x, f x = c • x := by

  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  refine ⟨c, ?_⟩
  have hne : Module.End.eigenspace f c ≠ ⊥ := hc
  have hinv : ∀ m ∈ M.ops, ∀ x ∈ Module.End.eigenspace f c,
      m x ∈ Module.End.eigenspace f c := by
    intro m hm x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hf m hm x, hx, map_smul]
  rcases hirr _ hinv with h | h
  · exact absurd h hne
  · intro x
    have hx : x ∈ Module.End.eigenspace f c := by rw [h]; trivial
    rw [Module.End.mem_eigenspace_iff] at hx
    exact hx

-- Prove2me | solution 1 for BookProof.ChapterSchurFiniteDimensional.isSchurFull_of_irreducible_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:25:39.880775+00:00
-- url     : https://prove2.me/submissions/63ae658c-64da-4954-ba72-21234b2df732

-- Generated from ChapterSchurFiniteDimensional.lean — solution of BookProof.ChapterSchurFiniteDimensional.isSchurFull_of_irreducible_finiteDimensional
import Mathlib
import Definitions.Def_ChapterSchurFiniteDimensional
import Definitions.Def_ChapterA
open BookProof.ChapterSchurFiniteDimensional



open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System
open BookProof.ChapterA
open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution [FiniteDimensional ℂ V] [Nontrivial V]
    (M : System ℂ V) (hirr : M.IsIrreducible) : IsSchurFull M := by

  intro S hS
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (S : V →ₗ[ℂ] V)
  set W : Submodule ℂ V := LinearMap.ker ((S : V →ₗ[ℂ] V) - c • LinearMap.id) with hW
  have hmemW : ∀ v : V, v ∈ W ↔ S v = c • v := by
    intro v
    simp only [hW, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    rfl
  have hWne : W ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := hc.exists_hasEigenvector
    intro hbot
    apply hv0
    have hvW : v ∈ W := (hmemW v).mpr (by simpa [Module.End.mem_eigenspace_iff] using hv)
    rw [hbot] at hvW
    simpa using hvW
  have hsub : M.IsSubsystem W := by
    refine ⟨W.closed_of_finiteDimensional, ?_⟩
    intro m hm w hw
    have hw' : S w = c • w := (hmemW w).mp hw
    refine (hmemW (m w)).mpr ?_
    have hcomm : S * m = m * S := hS m hm
    have h1 : S (m w) = m (S w) := by
      have := congrArg (fun T : V →L[ℂ] V => T w) hcomm
      simpa using this
    rw [h1, hw', map_smul]
  rcases hirr W hsub with h | h
  · exact absurd h hWne
  · refine ⟨c, ?_⟩
    ext x
    have hx : S x = c • x := (hmemW x).mp (by rw [h]; trivial)
    simpa using hx

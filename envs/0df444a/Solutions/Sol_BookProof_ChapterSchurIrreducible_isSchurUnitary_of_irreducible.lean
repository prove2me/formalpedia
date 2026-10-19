-- Prove2me | solution 1 for BookProof.ChapterSchurIrreducible.isSchurUnitary_of_irreducible
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:27:57.407982+00:00
-- url     : https://prove2.me/submissions/4cf6207d-d407-48c7-a84f-5224b45abd35
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSchurIrreducible.lean — solution of BookProof.ChapterSchurIrreducible.isSchurUnitary_of_irreducible
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Theorems.Thm_BookProof_ChapterSchurIrreducible_commutant_scalar_of_irreducible
import Definitions.Def_ChapterA
open BookProof.ChapterSchurIrreducible



open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System
open BookProof.ChapterA
open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial V] (M : System ℂ V) (hM : M.IsNormal)
    (hirr : M.IsIrreducible) : IsSchurUnitary M := by

  intro g hg
  set S : V →L[ℂ] V := g.toContinuousLinearEquiv.toContinuousLinearMap with hS
  have hSapp : ∀ x, S x = g x := fun _ => rfl
  have hcomm : M.Commutes S := by
    intro m hm
    ext x
    simp only [ContinuousLinearMap.mul_apply, hSapp]
    exact hg m hm x
  obtain ⟨c, hc⟩ := commutant_scalar_of_irreducible M hM hirr hcomm
  have hcx : ∀ x, g x = c • x := by
    intro x
    have := congrArg (fun T : V →L[ℂ] V => T x) hc
    simpa [hSapp] using this
  refine ⟨c, ?_, hcx⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hnorm : ‖g x‖ = ‖x‖ := g.norm_map x
  rw [hcx x, norm_smul] at hnorm
  have hxn : ‖x‖ ≠ 0 := by simpa using hx
  field_simp at hnorm
  exact hnorm

-- Prove2me | solution 1 for BookProof.ClosureUniqueness.opGraph_clExt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:05:54.619213+00:00
-- url     : https://prove2.me/submissions/9b37cf2a-5cbb-45a8-9b5e-8747b29d4172

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.opGraph_clExt
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) :
    opGraph (clExt T hdense hsym) = clGraph T := by

  apply le_antisymm
  · rintro p ⟨x, rfl⟩
    simpa using clFun_spec T x
  · intro p hp
    have hx : p.1 ∈ clDom T := mem_clDom_iff.2 ⟨p.2, by simpa using hp⟩
    refine ⟨⟨p.1, hx⟩, ?_⟩
    have : clFun T ⟨p.1, hx⟩ = p.2 := clFun_unique hdense hsym (by simpa using hp)
    simp [this]

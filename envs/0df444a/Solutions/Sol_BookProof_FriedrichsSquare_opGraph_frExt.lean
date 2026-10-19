-- Prove2me | solution 1 for BookProof.FriedrichsSquare.opGraph_frExt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:11:07.571857+00:00
-- url     : https://prove2.me/submissions/23801255-b298-44ad-b369-a6ee5e41ef90

-- Generated from ChapterFriedrichsSquareFactorization.lean — solution of BookProof.FriedrichsSquare.opGraph_frExt
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FriedrichsSquare




open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness
open BookProof.ClosureUniqueness
open BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    opGraph (frExt A hdense hsym) = factorRel A := by

  apply le_antisymm
  · rintro p ⟨x, rfl⟩
    simpa using frFun_spec A x
  · intro p hp
    have hx : p.1 ∈ frDom A := mem_frDom_iff.2 ⟨p.2, by simpa using hp⟩
    refine ⟨⟨p.1, hx⟩, ?_⟩
    have hval : frFun A ⟨p.1, hx⟩ = p.2 := frFun_unique hdense hsym (by simpa using hp)
    simp [hval]

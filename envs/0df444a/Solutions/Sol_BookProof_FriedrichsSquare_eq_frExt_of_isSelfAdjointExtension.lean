-- Prove2me | solution 1 for BookProof.FriedrichsSquare.eq_frExt_of_isSelfAdjointExtension
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:11:25.741387+00:00
-- url     : https://prove2.me/submissions/96c6af19-c012-48d8-a97e-0415a8731bec

-- Generated from ChapterFriedrichsSquareFactorization.lean — solution of BookProof.FriedrichsSquare.eq_frExt_of_isSelfAdjointExtension
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Theorems.Thm_BookProof_FriedrichsSquare_isFriedrichsSqExtension_iff_eq_factorRel
import Theorems.Thm_BookProof_FriedrichsSquare_opGraph_frExt
import Theorems.Thm_BookProof_ClosureUniqueness_eq_of_opGraph_eq
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
theorem solution [CompleteSpace F] {A : D →ₗ[ℂ] F}
    (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) {hstab : ∀ v : D, (A v : F) ∈ D}
    {Dom : Submodule ℂ F} {B : Dom →ₗ[ℂ] F} (hB : IsSelfAdjointExtension (sqOp A hstab) B)
    (hdomle : Dom ≤ clDom A) :
    Dom = frDom A ∧ ∀ (x : F) (h₁ : x ∈ Dom) (h₂ : x ∈ frDom A),
      B ⟨x, h₁⟩ = frExt A hdense hsym ⟨x, h₂⟩ := by

  have hspec : IsFriedrichsSqExtension A hstab (opGraph B) := by
    refine ⟨fun v => ?_, fun p hp => ?_, ?_⟩
    · obtain ⟨hv, hval⟩ := hB.1 v
      exact ⟨⟨(v : F), hv⟩, by simp [hval]⟩
    · obtain ⟨x, rfl⟩ := hp
      exact hdomle x.2
    · refine le_antisymm (fun p hp => ?_) (fun p hp q hq => ?_)
      · obtain ⟨hw, hval⟩ := hB.2.2 p.1 p.2 fun v => hp ((v : F), B v) ⟨v, rfl⟩
        exact ⟨⟨p.1, hw⟩, by simp [hval]⟩
      · obtain ⟨x, rfl⟩ := hp
        obtain ⟨y, rfl⟩ := hq
        exact hB.2.1 y x
  have hgraph : opGraph B = opGraph (frExt A hdense hsym) := by
    rw [(isFriedrichsSqExtension_iff_eq_factorRel hsym).1 hspec, opGraph_frExt]
  exact eq_of_opGraph_eq hgraph

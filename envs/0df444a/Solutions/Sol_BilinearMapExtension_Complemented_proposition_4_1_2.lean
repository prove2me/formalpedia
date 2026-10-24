-- Prove2me | solution 2 for BilinearMapExtension.Complemented.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:52:51.048438+00:00
-- url     : https://prove2.me/submissions/42e56540-b7d5-4338-bae1-92fcd6a3bad4

import Mathlib
import Definitions.Def_BilinearMapExtension_Complemented_Setting

namespace BilinearMapExtension.Complemented.ProjectionEquivalenceProof

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A bounded projection supplies a closed complementary kernel, without completeness. -/
theorem complemented_of_projection (S : Submodule 𝕜 X) (hS : IsClosed (S : Set X))
    (E : X →L[𝕜] X) (hE : IsProjectionOnto E S) : IsComplementedSubspace S := by
  have hcomp : S.ClosedComplemented := by
    refine ⟨E.codRestrict S hE.1, ?_⟩
    intro x
    apply Subtype.ext
    exact hE.2 x x.property
  exact ⟨hS, hcomp.exists_isClosed_isCompl⟩

/-- Closed algebraic complements in a Banach space supply bounded projections. -/
theorem exists_projection [CompleteSpace X] (S : Submodule 𝕜 X)
    (hS : IsComplementedSubspace S) : ∃ E : X →L[𝕜] X, IsProjectionOnto E S := by
  rcases hS with ⟨hS, T, hT, hST⟩
  let htop := Submodule.IsCompl.isTopCompl_of_isClosed hST hS hT
  refine ⟨S.projectionL T htop, ?_, ?_⟩
  · intro x
    exact (S.projectionOntoL T htop x).property
  · intro x hx
    exact congrArg Subtype.val (Submodule.projectionOntoL_apply_left htop (⟨x, hx⟩ : S))

end BilinearMapExtension.Complemented.ProjectionEquivalenceProof

open BilinearMapExtension.Complemented

/-- Kubrusly, Proposition 4.1: bounded projections and complemented subspaces. -/
theorem solution {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (S : Submodule 𝕜 X) (hS : IsClosed (S : Set X)) :
    ((∃ E : X →L[𝕜] X, IsProjectionOnto E S) → IsComplementedSubspace S) ∧
    ([CompleteSpace X] → IsComplementedSubspace S → ∃ E : X →L[𝕜] X, IsProjectionOnto E S) := by
  constructor
  · rintro ⟨E, hE⟩
    exact ProjectionEquivalenceProof.complemented_of_projection S hS E hE
  · intro inst hcomp
    exact ProjectionEquivalenceProof.exists_projection S hcomp

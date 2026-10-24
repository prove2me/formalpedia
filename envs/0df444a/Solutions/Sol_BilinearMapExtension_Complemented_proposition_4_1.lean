-- Prove2me | solution 1 for BilinearMapExtension.Complemented.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:52:08.860559+00:00
-- url     : https://prove2.me/submissions/2cce12e9-80dd-41f6-8996-e792626a7219

import Mathlib
import Definitions.Def_BilinearMapExtension_Complemented_Setting

open BilinearMapExtension.Complemented

/-- Proposition 4.1, p. 3. -/
theorem solution {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (S : Submodule 𝕜 X) (hS : IsClosed (S : Set X)) :
    ((∃ E : X →L[𝕜] X, IsProjectionOnto E S) → IsComplementedSubspace S) ∧
    ([CompleteSpace X] → IsComplementedSubspace S → ∃ E : X →L[𝕜] X, IsProjectionOnto E S) := by
  constructor
  · rintro ⟨E, hE⟩
    have hproj : S.ClosedComplemented := by
      refine ⟨E.codRestrict S hE.1, ?_⟩
      intro x
      apply Subtype.ext
      exact hE.2 x x.property
    exact ⟨hS, hproj.exists_isClosed_isCompl⟩
  · intro hX hcomp
    have hproj : S.ClosedComplemented :=
      Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl.mpr hcomp
    obtain ⟨P, hP⟩ := hproj
    refine ⟨S.subtypeL.comp P, ?_, ?_⟩
    · intro x
      exact (P x).property
    · intro x hx
      exact congrArg Subtype.val (hP ⟨x, hx⟩)

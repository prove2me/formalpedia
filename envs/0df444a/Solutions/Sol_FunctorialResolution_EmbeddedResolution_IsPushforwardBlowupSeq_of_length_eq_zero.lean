-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.of_length_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:21:41.7578+00:00
-- url     : https://prove2.me/submissions/9ee14f9d-6503-41ef-b9f2-3e89c24c9613

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq
namespace FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq
theorem _root_.solution {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X)
    (hS : BS.length = 0) (hX : B.length = 0) :
    IsPushforwardBlowupSeq j BS B := by
  have key : ∀ i : ℕ, i ≤ BS.length → i = 0 := fun i hi => by omega
  refine ⟨by omega, fun i hi =>
      eqToHom (congrArg BS.schemeAt (key i hi)) ≫ BS.isoZero.hom ≫ j ≫ B.isoZero.inv ≫
        eqToHom (congrArg B.schemeAt (key i hi).symm), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    infer_instance
  · simp
  · intro i hi
    exact absurd hi (by omega)
  · intro i hi
    exact absurd hi (by omega)
  · intro i hi
    exact absurd hi (by omega)
end FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq

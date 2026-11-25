-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.of_isStrictPullback_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:21:27.320191+00:00
-- url     : https://prove2.me/submissions/ef89a1bc-0170-444f-99e6-07cc4822c22a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_IsoBlowupPushforward
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_strictTransform_bot_of_isBlowupAlongIdealSheaf
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_isBlowupAlongIdealSheaf_blowupMorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_comap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
namespace IsPushforwardBlowupSeq
theorem _root_.solution {X' X : Scheme.{u}} (φ : X' ⟶ X)
    [IsIso φ] [IsClosedImmersion φ] {B' : SequenceOfBlowups X'} {B : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq φ B' B) : IsPushforwardBlowupSeq φ B' B := by
  obtain ⟨hlen, σ, hσ0, hsq, hc⟩ := h
  have hiso : ∀ (i : ℕ) (hi : i ≤ B'.length), IsIso (σ i hi) := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hz : σ 0 hi = B'.isoZero.hom ≫ φ ≫ B.isoZero.inv := by
          rw [← Category.assoc, ← hσ0]
          simp
        rw [hz]
        infer_instance
    | succ n ih =>
        intro hi
        have hn : n < B'.length := hi
        have := ih hn.le
        exact (hsq n hn).isIso_fst_of_isIso
  refine ⟨hlen, σ, ?_, hσ0, fun i hi => (hsq i hi).w, ?_, ?_⟩
  · intro i hi
    have := hiso i hi
    infer_instance
  · intro i hi
    have := hiso i hi.le
    rw [hc i hi, imageIdealSheaf_comap]
  · intro i hi
    have hi' : i < B.length := hlen ▸ hi
    have := hiso i hi.le
    have := hiso (i + 1) hi
    rw [Scheme.Hom.ker_eq_bot_of_isIso, Scheme.Hom.ker_eq_bot_of_isIso,
      strictTransform_bot_of_isBlowupAlongIdealSheaf (B.isBlowupAlongIdealSheaf_blowupMorphism i hi')]
end IsPushforwardBlowupSeq
end FunctorialResolution.EmbeddedResolution

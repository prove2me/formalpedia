-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.of_isomorphic_source
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:21:38.425317+00:00
-- url     : https://prove2.me/submissions/08b8eb6b-0022-48ea-863b-c45a3eaa2f2f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_StrictTransformClosedImmersion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_PushforwardComposition
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsPushforwardBlowupSeq_isIso_comp
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_comap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_eq_comap_inv


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
    {s s' : SequenceOfBlowups S} {t : SequenceOfBlowups X}
    (hs : s.Isomorphic s') (h : IsPushforwardBlowupSeq j s t) :
    IsPushforwardBlowupSeq j s' t := by
  obtain ⟨hlen, e, h0, hsqe, hce⟩ := hs
  have hpb : IsStrictPullbackBlowupSeq (𝟙 S) s' s := by
    refine ⟨hlen.symm, fun i hi => (e i (by omega)).inv, ?_, ?_, ?_⟩
    · show (e 0 (Nat.zero_le _)).inv ≫ s.isoZero.hom = s'.isoZero.hom ≫ 𝟙 S
      rw [Category.comp_id, ← h0, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    · intro i hi
      have hi' : i < s.length := by omega
      have hsq : (e (i + 1) hi').inv ≫ s.transitionMapSucc i
          = s'.transitionMapSucc i ≫ (e i hi'.le).inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, hsqe i hi', Category.assoc,
          Iso.hom_inv_id, Category.comp_id]
      show IsPullback ((e (i + 1) hi').inv) (s'.transitionMapSucc i) (s.transitionMapSucc i)
        ((e i hi'.le).inv)
      exact IsPullback.of_horiz_isIso ⟨hsq⟩
    · intro i hi
      have hi' : i < s.length := by omega
      have h1 : imageIdealSheaf (e i hi'.le).hom ((s'.center i).comap (e i hi'.le).hom)
          = imageIdealSheaf (e i hi'.le).hom (s.center i) := by rw [hce i hi']
      rw [imageIdealSheaf_comap] at h1
      have h2 : inv (e i hi'.le).hom = (e i hi'.le).inv :=
        IsIso.inv_eq_of_hom_inv_id (Iso.hom_inv_id (e i hi'.le))
      show s'.center i = (s.center i).comap ((e i hi'.le).inv)
      rw [h1, imageIdealSheaf_eq_comap_inv, h2]
  exact IsPushforwardBlowupSeq.isIso_comp (𝟙 S) j j (Category.id_comp j).symm hpb h
end FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq

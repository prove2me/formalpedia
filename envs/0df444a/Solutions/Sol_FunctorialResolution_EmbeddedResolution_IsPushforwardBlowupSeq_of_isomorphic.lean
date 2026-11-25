-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.of_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:21:33.910971+00:00
-- url     : https://prove2.me/submissions/a5ea3aa0-1df3-4501-a2e5-bc2f9c82f019

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_comap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ker_comp_eq_imageIdealSheaf_ker
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_strictTransform_of_comm_sq
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_comp


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
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (h : IsPushforwardBlowupSeq j BS B) (he : B.Isomorphic B') :
    IsPushforwardBlowupSeq j BS B' := by
  obtain ⟨hlen, σ, hci, h0, hstep, hcent, hker⟩ := h
  obtain ⟨hlen2, e, he0, hestep, hecent⟩ := he
  have hestep' : ∀ (i : ℕ) (hp : i + 1 ≤ B.length) (hq : i ≤ B.length),
      (e (i + 1) hp).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ (e i hq).hom :=
    fun i hp _ => hestep i hp
  have hecent' : ∀ (i : ℕ) (hp : i < B.length) (hq : i ≤ B.length),
      (B'.center i).comap (e i hq).hom = B.center i := fun i hp _ => hecent i hp
  refine ⟨by omega, fun i hi => σ i hi ≫ (e i (by omega)).hom, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := hci i hi
    infer_instance
  · have hgoal : (σ 0 (Nat.zero_le _) ≫ (e 0 (Nat.zero_le _)).hom) ≫ B'.isoZero.hom
        = BS.isoZero.hom ≫ j := by
      rw [Category.assoc, he0, h0]
    exact hgoal
  · intro i hi
    have hiB : i < B.length := by omega
    have hgoal : (σ (i + 1) hi ≫ (e (i + 1) hiB).hom) ≫ B'.transitionMapSucc i
        = BS.transitionMapSucc i ≫ (σ i hi.le ≫ (e i hiB.le).hom) := by
      rw [Category.assoc, hestep' i hiB hiB.le, ← Category.assoc, hstep i hi, Category.assoc]
    exact hgoal
  · intro i hi
    have hiB : i < B.length := by omega
    have hgoal : imageIdealSheaf (σ i hi.le ≫ (e i hiB.le).hom) (BS.center i) = B'.center i := by
      rw [imageIdealSheaf_comp, ← hcent i hi, ← hecent' i hiB hiB.le,
        imageIdealSheaf_comap]
    exact hgoal.symm
  · intro i hi
    have hiB : i < B.length := by omega
    have hcen : imageIdealSheaf (e i hiB.le).hom (B.center i) = B'.center i := by
      rw [← hecent' i hiB hiB.le, imageIdealSheaf_comap]
    have hgoal : (σ (i + 1) hi ≫ (e (i + 1) hiB).hom).ker
        = Blowup.strictTransform (B'.transitionMapSucc i) (B'.center i)
            ((σ i hi.le ≫ (e i hiB.le).hom).ker) := by
      rw [ker_comp_eq_imageIdealSheaf_ker, hker i hi,
        imageIdealSheaf_strictTransform_of_comm_sq (B.transitionMapSucc i) (B'.transitionMapSucc i)
          (e i hiB.le).hom (e (i + 1) hiB).hom (hestep' i hiB hiB.le) (B.center i)
          ((σ i hi.le).ker),
        hcen, ker_comp_eq_imageIdealSheaf_ker]
    exact hgoal
end FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq

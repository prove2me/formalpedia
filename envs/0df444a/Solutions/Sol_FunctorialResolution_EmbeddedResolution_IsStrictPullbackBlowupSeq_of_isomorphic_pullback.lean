-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.of_isomorphic_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:47.68783+00:00
-- url     : https://prove2.me/submissions/27ca2e7a-0029-4f15-bc0a-a75e2dc42d52

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_symm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_trans


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
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
namespace FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
theorem _root_.solution {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t t' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (he : t.Isomorphic t') :
    IsStrictPullbackBlowupSeq g t' s := by
  have hlen : t.length = s.length := h.1
  obtain ⟨σ, hzero, hpb, hcen⟩ := h.2
  have hlen' : t.length = t'.length := he.1
  obtain ⟨e, hezero, hestep, hecen⟩ := he.2
  have hconv : ∀ i : ℕ, i ≤ t'.length → i ≤ t.length := fun i hi => by omega
  refine ⟨hlen'.symm.trans hlen,
    fun i hi => (e i (hconv i hi)).inv ≫ σ i (hconv i hi), ?_, ?_, ?_⟩
  · have key : ((e 0 (hconv 0 (Nat.zero_le t'.length))).inv ≫
        σ 0 (hconv 0 (Nat.zero_le t'.length))) ≫ s.isoZero.hom = t'.isoZero.hom ≫ g := by
      rw [Category.assoc, hzero, Iso.inv_comp_eq, ← Category.assoc, hezero]
    exact key
  · intro i hi
    have hi' : i < t.length := by omega
    have hsq : CommSq (e (i + 1) hi').inv (t'.transitionMapSucc i) (t.transitionMapSucc i) (e i hi'.le).inv := by
      refine ⟨?_⟩
      rw [Iso.inv_comp_eq, ← Category.assoc, hestep i hi', Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    exact (IsPullback.of_horiz_isIso hsq).paste_horiz (hpb i hi')
  · intro i hi
    have hi' : i < t.length := by omega
    have key : t'.center i = (s.center i).comap ((e i hi'.le).inv ≫ σ i hi'.le) := by
      rw [Scheme.IdealSheafData.comap_comp, ← hcen i hi', ← hecen i hi',
        ← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
    exact key
end FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq

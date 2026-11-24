-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_isomorphic_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:50:24.920436+00:00
-- url     : https://prove2.me/submissions/53f6dee5-c32a-4ee1-a087-34e2bfd06389

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IsoBlowupRemoval
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_symm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_blowupMorphism_eq_transitionMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_nontrivialIndex_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_objNontrivialIndexZeroIso_hom
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_transitionMap_self
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_blowupMorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_isoObjZero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_schemeAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.nontrivialIndex_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_center
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_schemeAt


section
universe u
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
namespace SequenceOfBlowups
private theorem transitionMap_eq_eqToHom {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b : ℕ} (h : a ≤ b)
    (h' : a = b) : s.transitionMap h = eqToHom (congrArg s.schemeAt h'.symm) := by
  subst h'
  rw [s.transitionMap_self h, eqToHom_refl]
private theorem center_comap_eqToHom {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b : ℕ} (h : a = b) :
    (s.center b).comap (eqToHom (congrArg s.schemeAt h)) = s.center a := by
  subst h
  simp
end SequenceOfBlowups
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
namespace FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
theorem _root_.solution {X : Scheme.{u}} (t : SequenceOfBlowups X)
    (h : ∀ i : ℕ, i < t.length → t.center i ≠ ⊤) : t.withoutIsoBlowups.Isomorphic t := by
  have hnext : ∀ a : ℕ, t.nextNontrivialIndex a = a := by
    intro a
    refine le_antisymm (t.nextNontrivialIndex_le le_rfl ?_) (t.le_nextNontrivialIndex a)
    by_cases ha : a < t.length
    · exact Or.inl (h a ha)
    · exact Or.inr (by omega)
  have hret : ∀ j : ℕ, t.nontrivialIndex j = j := by
    intro j
    induction j with
    | zero => rw [t.nontrivialIndex_zero, hnext]
    | succ j ih => rw [t.nontrivialIndex_succ, hnext, ih]
  have hplen : t.withoutIsoBlowups.length = t.length := by
    have h2 := t.nontrivialIndex_lengthWithoutIsoBlowups
    rw [hret] at h2
    exact h2
  have h1 : (eqToIso (congrArg t.schemeAt (hret 0))).hom ≫ t.isoZero.hom = t.withoutIsoBlowups.isoZero.hom := by
    rw [t.withoutIsoBlowups_isoObjZero, t.objNontrivialIndexZeroIso_hom, t.projectionToBase_def,
      t.transitionMap_eq_eqToHom _ (hret 0).symm]
    rfl
  have h2 : ∀ i : ℕ, i < t.withoutIsoBlowups.length →
      (eqToIso (congrArg t.schemeAt (hret (i + 1)))).hom ≫ t.transitionMapSucc i
        = t.withoutIsoBlowups.transitionMapSucc i ≫ (eqToIso (congrArg t.schemeAt (hret i))).hom := by
    intro i _
    rw [t.withoutIsoBlowups_blowupMorphism, t.blowupMorphism_eq_transitionMap]
    exact t.eqToHom_comp_transitionMap (hret i) (hret (i + 1)) _ _
  have h3 : ∀ i : ℕ, i < t.withoutIsoBlowups.length →
      (t.center i).comap (eqToIso (congrArg t.schemeAt (hret i))).hom = t.withoutIsoBlowups.center i := by
    intro i _
    exact t.center_comap_eqToHom (hret i)
  unfold SequenceOfBlowups.Isomorphic
  exact ⟨hplen, fun i _ => eqToIso (congrArg t.schemeAt (hret i)), h1, h2, h3⟩
end FunctorialResolution.EmbeddedResolution.SequenceOfBlowups

-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.Isomorphic.exists_lastObjIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:47:37.362661+00:00
-- url     : https://prove2.me/submissions/74b1e3f9-26be-4ba8-85ea-72ef6ef24d72

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_lastStructMap_eq_projectionToBase
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem eqToIso_hom_comp_projectionToBase_of_eq {X : Scheme.{u}} (s : SequenceOfBlowups X) {i j : ℕ}
    (hij : i = j) : (eqToIso (congrArg s.schemeAt hij)).hom ≫ s.projectionToBase j = s.projectionToBase i := by
  subst hij
  simp
private theorem iso_hom_comp_projectionToBase_of_commute_blowupMorphism {X : Scheme.{u}} {B B' : SequenceOfBlowups X}
    (e : ∀ i : ℕ, i ≤ B.length → (B.schemeAt i ≅ B'.schemeAt i))
    (h0 : (e 0 (Nat.zero_le _)).hom ≫ B'.isoZero.hom = B.isoZero.hom)
    (hstep : ∀ i : ℕ, ∀ hi : i < B.length,
        (e (i + 1) hi).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ (e i hi.le).hom) :
    ∀ (i : ℕ) (hi : i ≤ B.length), (e i hi).hom ≫ B'.projectionToBase i = B.projectionToBase i := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [B'.projectionToBase_zero, B.projectionToBase_zero]
    exact h0
  | succ n ih =>
    intro hi
    have hn : n < B.length := hi
    rw [B'.projectionToBase_succ, B.projectionToBase_succ, ← Category.assoc]
    show ((e (n + 1) hn).hom ≫ B'.transitionMapSucc n) ≫ B'.projectionToBase n
      = B.transitionMapSucc n ≫ B.projectionToBase n
    rw [hstep n hn, Category.assoc, ih hn.le]
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
namespace SequenceOfBlowups.Isomorphic
theorem _root_.solution {X : Scheme.{u}} {B B' : SequenceOfBlowups X}
    (h : B.Isomorphic B') :
    ∃ e : B.lastObj ≅ B'.lastObj, e.hom ≫ B'.lastStructMap = B.lastStructMap := by
  obtain ⟨hL, e, h0, hstep, _⟩ := h
  refine ⟨e B.length le_rfl ≪≫ eqToIso (congrArg B'.schemeAt hL), ?_⟩
  rw [SequenceOfBlowups.lastStructMap_eq_projectionToBase, SequenceOfBlowups.lastStructMap_eq_projectionToBase, Iso.trans_hom,
    Category.assoc, eqToIso_hom_comp_projectionToBase_of_eq B' hL]
  exact iso_hom_comp_projectionToBase_of_commute_blowupMorphism e h0 hstep B.length le_rfl
end SequenceOfBlowups.Isomorphic
end FunctorialResolution.EmbeddedResolution

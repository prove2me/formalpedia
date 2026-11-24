-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence.of_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:32.896249+00:00
-- url     : https://prove2.me/submissions/6119e30c-156b-4edf-a293-ceed53b3a258

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceIsomorphism
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
private theorem iso_hom_comp_projectionToBase {X' : Scheme.{u}} {s' s'' : SequenceOfBlowups X'}
    (ε : ∀ i : ℕ, i ≤ s'.length → (s'.schemeAt i ≅ s''.schemeAt i))
    (h0 : (ε 0 (Nat.zero_le _)).hom ≫ s''.isoZero.hom = s'.isoZero.hom)
    (hst : ∀ i : ℕ, ∀ hi : i < s'.length,
      (ε (i + 1) hi).hom ≫ s''.transitionMapSucc i = s'.transitionMapSucc i ≫ (ε i hi.le).hom) :
    ∀ i : ℕ, ∀ hi : i ≤ s'.length, (ε i hi).hom ≫ s''.projectionToBase i = s'.projectionToBase i := by
  intro i
  induction i with
  | zero =>
    intro hi
    rw [s''.projectionToBase_zero, s'.projectionToBase_zero]
    exact h0
  | succ n ih =>
    intro hi
    rw [s''.projectionToBase_succ n, s'.projectionToBase_succ n, ← Category.assoc,
      hst n hi, Category.assoc, ih (Nat.le_of_succ_le hi)]
namespace IsPullbackBlowupSequence
end IsPullbackBlowupSequence
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence
namespace FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence
theorem _root_.solution {X X' : Scheme.{u}} {φ : X' ⟶ X} {s : SequenceOfBlowups X} {s' s'' : SequenceOfBlowups X'}
    (h : IsPullbackBlowupSequence φ s' s) (e : s'.Isomorphic s'') : IsPullbackBlowupSequence φ s'' s := by
  obtain ⟨r, E, hr1, hr2, hr3, hr4, hfst, hstepE, hcen⟩ := h
  obtain ⟨hlen, ε, h0, hst, hc⟩ := e
  have hcl : ∀ i : ℕ, i ≤ s''.length → i ≤ s'.length := fun i hi => le_of_le_of_eq hi hlen.symm
  have hcl' : ∀ i : ℕ, i < s''.length → i < s'.length := fun i hi => lt_of_lt_of_eq hi hlen.symm
  have hproj := iso_hom_comp_projectionToBase ε h0 hst
  refine ⟨r, fun i hi => (ε i (hcl i hi)).symm ≪≫ E i (hcl i hi),
    fun i hi => hr1 i (hcl' i hi), fun i j hj hij => hr2 i j (hcl j hj) hij,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hlen]; exact hr3
  · intro i hi
    rw [hr4 i hi, hlen]
  · intro i hi
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hfst i (hcl i hi)]
    rw [← hproj i (hcl i hi)]
    simp
  · intro i hi hr
    have h1 := hstepE i (hcl' i hi) hr
    have h2 := hst i (hcl' i hi)
    have key : s''.transitionMapSucc i ≫ (ε i (hcl i hi.le)).inv
        = (ε (i + 1) (hcl' i hi)).inv ≫ s'.transitionMapSucc i := by
      rw [← Iso.cancel_iso_hom_left (ε (i + 1) (hcl' i hi)), ← Category.assoc, h2]
      simp
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, key, Category.assoc, h1, Category.assoc]
  · intro i hi
    have h1 := hcen i (hcl' i hi)
    have h2 := hc i (hcl' i hi)
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [Scheme.IdealSheafData.comap_comp, ← h1, ← h2, ← Scheme.IdealSheafData.comap_comp,
      Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
end FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence

-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.Isomorphic.symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:11.819806+00:00
-- url     : https://prove2.me/submissions/1da30510-94c8-4b2a-92c2-0e6675c50ec5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
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
private theorem iso_inv_comp_eq_comp_inv {W Y Z T : Scheme.{u}} (a : W ≅ Y) (b : Z ≅ T)
    (p : W ⟶ Z) (q : Y ⟶ T) (hw : a.hom ≫ q = p ≫ b.hom) :
    a.inv ≫ p = q ≫ b.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, Iso.hom_inv_id, Category.comp_id]
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
    (h : B.Isomorphic B') : B'.Isomorphic B := by
  obtain ⟨hL, e, h0, hstep, hcen⟩ := h
  have p1 : (e 0 (Nat.zero_le _)).inv ≫ B.isoZero.hom = B'.isoZero.hom := by
    rw [Iso.inv_comp_eq]
    exact h0.symm
  have p2 : ∀ (i : ℕ) (hi : i < B'.length),
      (e (i + 1) (by omega)).inv ≫ B.transitionMapSucc i
        = B'.transitionMapSucc i ≫ (e i (by omega)).inv := by
    intro i hi
    have hi' : i < B.length := by omega
    exact iso_inv_comp_eq_comp_inv (e (i + 1) hi') (e i hi'.le) (B.transitionMapSucc i)
      (B'.transitionMapSucc i) (hstep i hi')
  have p3 : ∀ (i : ℕ) (hi : i < B'.length),
      (B.center i).comap (e i (by omega)).inv = B'.center i := by
    intro i hi
    have hi' : i < B.length := by omega
    rw [← hcen i hi', ← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  exact ⟨hL.symm, fun i hi => (e i (by omega)).symm, p1, p2, p3⟩
end SequenceOfBlowups.Isomorphic
end FunctorialResolution.EmbeddedResolution

-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.Isomorphic.trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:11:47.880951+00:00
-- url     : https://prove2.me/submissions/8a4493b8-d476-482a-bd37-a832d375bd34

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
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
namespace SequenceOfBlowups.Isomorphic
theorem _root_.solution {X : Scheme.{u}} {B B' B'' : SequenceOfBlowups X}
    (h : B.Isomorphic B') (h' : B'.Isomorphic B'') : B.Isomorphic B'' := by
  obtain ⟨hL, e, h0, hstep, hcen⟩ := h
  obtain ⟨hL', g, g0, gstep, gcen⟩ := h'
  have p1 : ((e 0 (Nat.zero_le _)).hom ≫ (g 0 (Nat.zero_le _)).hom) ≫ B''.isoZero.hom
      = B.isoZero.hom := by
    rw [Category.assoc, g0, h0]
  have p2 : ∀ (i : ℕ) (hi : i < B.length),
      ((e (i + 1) hi).hom ≫ (g (i + 1) (by omega)).hom) ≫ B''.transitionMapSucc i
        = B.transitionMapSucc i ≫ ((e i hi.le).hom ≫ (g i (by omega)).hom) := by
    intro i hi
    have hi' : i < B'.length := by omega
    rw [Category.assoc, gstep i hi', ← Category.assoc, hstep i hi, Category.assoc]
  have p3 : ∀ (i : ℕ) (hi : i < B.length),
      (B''.center i).comap ((e i hi.le).hom ≫ (g i (by omega)).hom) = B.center i := by
    intro i hi
    have hi' : i < B'.length := by omega
    rw [Scheme.IdealSheafData.comap_comp, gcen i hi', hcen i hi]
  exact ⟨hL.trans hL', fun i hi => (e i hi) ≪≫ (g i (by omega)), p1, p2, p3⟩
end SequenceOfBlowups.Isomorphic
end FunctorialResolution.EmbeddedResolution

-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.iso_hom_comp_projectionToBase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:01:30.102148+00:00
-- url     : https://prove2.me/submissions/4944ed2c-27ae-4d36-9ca5-c06f655aed02

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_iso_hom_comp_transitionMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_trans
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_def


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
namespace FunctorialResolution.EmbeddedResolution
namespace SequenceOfBlowups
theorem _root_.solution {X : Scheme.{u}} (s t : SequenceOfBlowups X) (L : ℕ)
    (e : ∀ i : ℕ, i ≤ L → (s.schemeAt i ≅ t.schemeAt i))
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      (e (i + 1) hi).hom ≫ t.transitionMapSucc i = s.transitionMapSucc i ≫ (e i hi.le).hom)
    (hzero : (e 0 (Nat.zero_le _)).hom ≫ t.isoZero.hom = s.isoZero.hom) :
    ∀ b : ℕ, ∀ hb : b ≤ L, (e b hb).hom ≫ t.projectionToBase b = s.projectionToBase b := by
  intro b hb
  have hd := FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.iso_hom_comp_transitionMap s t L e hstep 0 b (Nat.zero_le b) hb
  have h0 : (e 0 ((Nat.zero_le b).trans hb)).hom ≫ t.isoZero.hom = s.isoZero.hom := hzero
  rw [FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_def, FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_def, ← Category.assoc,
    hd, Category.assoc, h0]
end SequenceOfBlowups
end FunctorialResolution.EmbeddedResolution

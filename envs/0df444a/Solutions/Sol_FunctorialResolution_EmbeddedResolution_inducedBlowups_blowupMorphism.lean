-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.inducedBlowups_blowupMorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:38:36.121557+00:00
-- url     : https://prove2.me/submissions/93820d7e-a1a7-4c07-b3b1-2d930b0f7227

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrictTransformTower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_totalTower_map_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_blowupMorphism_eq_transitionMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_transitionMap_def


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups) (i : ℕ) :
    (S.inducedBlowups h).transitionMapSucc i = S.totalTransition i := by
  have h1 : (S.inducedBlowups h).transitionMapSucc i = (S.inducedBlowups h).transitionMap (Nat.le_succ i) :=
    SequenceOfBlowups.blowupMorphism_eq_transitionMap (S.inducedBlowups h) i
  have h2 : (S.inducedBlowups h).transitionMap (Nat.le_succ i)
      = (S.inducedBlowups h).tower.map (homOfLE (Nat.le_succ i)).op :=
    SequenceOfBlowups.transitionMap_def (S.inducedBlowups h) (Nat.le_succ i)
  rw [h1, h2]
  exact S.totalTower_map_succ i
end FunctorialResolution.EmbeddedResolution

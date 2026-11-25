-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.BlowupSequenceData.ofSequenceOfBlowups_projectionToBase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:21:51.254446+00:00
-- url     : https://prove2.me/submissions/b7bb8433-f40a-4abb-89fe-89b9d16603de

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_BlowupSequenceData
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_blowupMorphism_eq_transitionMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_def
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
open CategoryTheory Opposite AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.BlowupSequenceData
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution.BlowupSequenceData
theorem _root_.solution (s : SequenceOfBlowups X) (i : ℕ) : projectionToBase (ofSequenceOfBlowups s) i = s.projectionToBase i := by
  induction i with
  | zero =>
    have h1 : s.tower.map (CategoryTheory.homOfLE (le_refl (0 : ℕ))).op = 𝟙 (s.tower.obj (Opposite.op 0)) :=
      s.tower.map_id (Opposite.op 0)
    have h2 : s.projectionToBase 0 = s.isoZero.hom := by
      rw [SequenceOfBlowups.projectionToBase_def, SequenceOfBlowups.transitionMap_def, h1, Category.id_comp]
    exact h2.symm
  | succ i ih =>
    show (ofSequenceOfBlowups s).map i ≫ projectionToBase (ofSequenceOfBlowups s) i = s.projectionToBase (i + 1)
    rw [ih]
    show s.transitionMapSucc i ≫ s.projectionToBase i = s.projectionToBase (i + 1)
    rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_comp_projectionToBase]
end FunctorialResolution.EmbeddedResolution.BlowupSequenceData

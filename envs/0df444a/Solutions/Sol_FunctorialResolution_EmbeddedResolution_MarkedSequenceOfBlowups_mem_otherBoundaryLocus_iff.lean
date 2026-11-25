-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.mem_otherBoundaryLocus_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:21:41.937571+00:00
-- url     : https://prove2.me/submissions/8b1c414e-8699-434d-8793-c30c378f5613

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificateMonotone
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReductionProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
namespace FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups
theorem _root_.solution (s : MarkedSequenceOfBlowups p I m E) (j t : ℕ)
    (x : ↥(s.toSequenceOfBlowups.schemeAt t)) :
    x ∈ s.otherBoundaryLocus j t ↔
      ∃ i : Fin (s.boundary t).length, (i : ℕ) ≠ j ∧
        x ∈ (((s.boundary t).get i).support : Set ↥(s.toSequenceOfBlowups.schemeAt t)) := by
  constructor
  · intro hx
    have hx' : x ∈ ⋃ (i : Fin (s.boundary t).length) (_ : (i : ℕ) ≠ j),
        (((s.boundary t).get i).support : Set ↥(s.toSequenceOfBlowups.schemeAt t)) := hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx'
    exact ⟨i, hi, hxi⟩
  · rintro ⟨i, hi, hxi⟩
    have hx' : x ∈ ⋃ (i : Fin (s.boundary t).length) (_ : (i : ℕ) ≠ j),
        (((s.boundary t).get i).support : Set ↥(s.toSequenceOfBlowups.schemeAt t)) :=
      Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩
    exact hx'
end FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups

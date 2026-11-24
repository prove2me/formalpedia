-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.mem_boundaryLocus_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:15:51.582062+00:00
-- url     : https://prove2.me/submissions/b5acfd6a-29ad-477b-a31b-7e9067bfd60a

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
theorem _root_.solution (s : MarkedSequenceOfBlowups p I m E) (t : ℕ)
    (x : ↥(s.toSequenceOfBlowups.schemeAt t)) :
    x ∈ s.boundaryLocus t ↔
      ∃ D ∈ s.boundary t, x ∈ ((D.support : Set ↥(s.toSequenceOfBlowups.schemeAt t))) := by
  constructor
  · intro hx
    have hx' : x ∈ ⋃ D ∈ s.boundary t, ((D.support : Set ↥(s.toSequenceOfBlowups.schemeAt t))) := hx
    obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.mp hx'
    exact ⟨D, hD, hxD⟩
  · rintro ⟨D, hD, hxD⟩
    have hx' : x ∈ ⋃ D ∈ s.boundary t, ((D.support : Set ↥(s.toSequenceOfBlowups.schemeAt t))) :=
      Set.mem_iUnion₂.mpr ⟨D, hD, hxD⟩
    exact hx'
end FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups

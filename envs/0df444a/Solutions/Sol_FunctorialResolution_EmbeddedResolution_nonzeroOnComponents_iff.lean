-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.nonzeroOnComponents_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:17.465537+00:00
-- url     : https://prove2.me/submissions/8e582e45-accb-40e4-a3ba-193be8f0fa8f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} (I : X.IdealSheafData) :
    NonzeroOnComponents I ↔ ∀ T ∈ irreducibleComponents (↥X), ¬ T ⊆ (I.support : Set ↥X) :=
  Iff.rfl
end FunctorialResolution.EmbeddedResolution

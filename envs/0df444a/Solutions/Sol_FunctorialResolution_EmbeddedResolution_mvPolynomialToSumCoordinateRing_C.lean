-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mvPolynomialToSumCoordinateRing_C
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-23T23:49:35.30211+00:00
-- url     : https://prove2.me/submissions/ad8c2e21-f0f4-4d91-8fb9-dad584206956

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_ExtendCoordinatesToAffineSpace
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PolynomialRingOverGlobalSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution


theorem solution (k : Type u) [Field k] (M n : ℕ)
    (t : Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    mvPolynomialToSumCoordinateRing k M n (MvPolynomial.C t) = (projLeft k M n).appTop t := by
  simp [mvPolynomialToSumCoordinateRing]

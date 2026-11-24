-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mvPolynomialToSumCoordinateRing_X
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-23T23:49:36.392982+00:00
-- url     : https://prove2.me/submissions/14ff8c3a-1de1-4cbf-b143-3becc3953355

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


theorem solution (k : Type u) [Field k] (M n : ℕ) (i : Fin n) :
    mvPolynomialToSumCoordinateRing k M n (MvPolynomial.X i) =
      AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n)) := by
  simp [mvPolynomialToSumCoordinateRing]

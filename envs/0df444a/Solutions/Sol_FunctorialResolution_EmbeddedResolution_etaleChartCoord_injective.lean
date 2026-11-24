-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.etaleChartCoord_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:31:17.415536+00:00
-- url     : https://prove2.me/submissions/e7965f33-cc33-4feb-b1c1-fff4084b200e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorRadical
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_etaleChartCoord_def

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
namespace FunctorialResolution.EmbeddedResolution
private theorem algebraMap_coordPolynomialRing_injective_of_etale (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    [Nontrivial S] : Function.Injective (algebraMap (CoordPolynomialRing k m) S) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro a ha
  by_contra h
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := S)
    (mem_nonZeroDivisors_of_ne_zero h)
  have h1 : (1 : S) = 0 := by
    apply hreg
    show a • (1 : S) = a • (0 : S)
    rw [smul_zero, Algebra.smul_def, ha, zero_mul]
  exact one_ne_zero h1
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    [Nontrivial S] : Function.Injective (etaleChartCoord k m S) := by
  have hinj := algebraMap_coordPolynomialRing_injective_of_etale k m S
  intro i j hij
  have h : (MvPolynomial.X (ULift.up i) : CoordPolynomialRing k m)
      = MvPolynomial.X (ULift.up j) := by
    apply hinj
    rw [← etaleChartCoord_def, ← etaleChartCoord_def]
    exact hij
  exact congrArg ULift.down (MvPolynomial.X_injective h)
end FunctorialResolution.EmbeddedResolution

-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isRadical_span_singleton_prod_algebraMap_etaleChartCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:58:33.363797+00:00
-- url     : https://prove2.me/submissions/7f804cf8-14f1-4b92-a9fe-a38a94880731

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorRadical
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_linearIndependent_toCotangent_etaleChartCoord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_of_isLocalization_etale
import Theorems.Thm_IsRegularLocalRing_isRadical_span_singleton_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q) :
    (Ideal.span ({∏ j ∈ J, algebraMap S A (etaleChartCoord k m S j)} : Set A)).IsRadical := by
  classical
  have hreg : IsRegularLocalRing A := isRegularLocalRing_of_isLocalization_etale k m S q A
  have hJA : ∀ j ∈ J, algebraMap S A (etaleChartCoord k m S j) ∈ IsLocalRing.maximalIdeal A := by
    intro j hj
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q
      (etaleChartCoord k m S j)).mpr (hJ j hj)
  have hli := linearIndependent_toCotangent_etaleChartCoord k m S q A J hJ hJA
  have hmain := _root_.IsRegularLocalRing.isRadical_span_singleton_prod
    (fun j : { x : Fin m // x ∈ J } => algebraMap S A (etaleChartCoord k m S (j : Fin m)))
    (fun j => hJA (j : Fin m) j.2) hli
  rw [← Finset.prod_coe_sort J (fun j => algebraMap S A (etaleChartCoord k m S j))]
  exact hmain
end FunctorialResolution.EmbeddedResolution

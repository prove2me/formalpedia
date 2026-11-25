-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isPrime_span_singleton_algebraMap_etaleChartCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:58:31.983712+00:00
-- url     : https://prove2.me/submissions/f9eabfdb-a791-4ad5-942e-778cfb69e841

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorRadical
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisibility
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_of_isLocalization_etale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_linearIndependent_toCotangent_etaleChartCoord
import Theorems.Thm_IsRegularLocalRing_isPrime_span_singleton


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
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (j : Fin m)
    (hj : etaleChartCoord k m S j ∈ q) :
    (Ideal.span ({algebraMap S A (etaleChartCoord k m S j)} : Set A)).IsPrime := by
  have : IsRegularLocalRing A := isRegularLocalRing_of_isLocalization_etale k m S q A
  have hJ : ∀ i ∈ ({j} : Finset (Fin m)), etaleChartCoord k m S i ∈ q := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact hj
  have hJA : ∀ i ∈ ({j} : Finset (Fin m)),
      algebraMap S A (etaleChartCoord k m S i) ∈ IsLocalRing.maximalIdeal A := by
    intro i hi
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q _).mpr (hJ i hi)
  have hli := linearIndependent_toCotangent_etaleChartCoord k m S q A {j} hJ hJA
  exact IsRegularLocalRing.isPrime_span_singleton
    (fun i : { x : Fin m // x ∈ ({j} : Finset (Fin m)) } =>
      algebraMap S A (etaleChartCoord k m S (i : Fin m)))
    (fun i => hJA (i : Fin m) i.2) hli ⟨j, Finset.mem_singleton_self j⟩
end FunctorialResolution.EmbeddedResolution

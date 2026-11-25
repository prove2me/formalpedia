-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isRadical_map_span_singleton_prod_etaleChartCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:05:23.139903+00:00
-- url     : https://prove2.me/submissions/4f83db15-abf7-4c6b-86ca-3531b8662c9a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorRadical
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRadical_span_singleton_prod_algebraMap_etaleChartCoord

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
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (T : Finset (Fin m)) :
    (Ideal.map (algebraMap S A)
      (Ideal.span ({∏ j ∈ T, etaleChartCoord k m S j} : Set S))).IsRadical := by
  classical
  obtain ⟨J, hJdef⟩ : ∃ J : Finset (Fin m),
      J = T.filter (fun j => etaleChartCoord k m S j ∈ q) := ⟨_, rfl⟩
  have hJsub : J ⊆ T := by rw [hJdef]; exact Finset.filter_subset _ _
  have hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q := by
    intro j hj
    rw [hJdef] at hj
    exact (Finset.mem_filter.mp hj).2
  have hunit : IsUnit (∏ j ∈ T \ J, algebraMap S A (etaleChartCoord k m S j)) := by
    refine Finset.prod_induction _ _ (fun u v hu hv => hu.mul hv) isUnit_one ?_
    intro j hj
    have h1 := Finset.mem_sdiff.mp hj
    have hj' : etaleChartCoord k m S j ∉ q := by
      intro hmem
      exact h1.2 (by rw [hJdef]; exact Finset.mem_filter.mpr ⟨h1.1, hmem⟩)
    exact IsLocalization.map_units A (⟨etaleChartCoord k m S j, hj'⟩ : q.primeCompl)
  have hsplit : ∏ j ∈ T, algebraMap S A (etaleChartCoord k m S j)
      = (∏ j ∈ T \ J, algebraMap S A (etaleChartCoord k m S j)) *
        ∏ j ∈ J, algebraMap S A (etaleChartCoord k m S j) := by
    rw [← Finset.prod_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hJsub]
  rw [Ideal.map_span, Set.image_singleton, map_prod, hsplit,
    Ideal.span_singleton_mul_left_unit hunit _]
  exact isRadical_span_singleton_prod_algebraMap_etaleChartCoord k m S q A J hJ
end FunctorialResolution.EmbeddedResolution

-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isRegularLocalRing_quotient_map_etaleChartCoordIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:20:37.981125+00:00
-- url     : https://prove2.me/submissions/1337160f-b5f4-4ed3-9267-f057221803c3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_etaleChartCoordIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_mvPolynomialCoordIdeal_eq_etaleChartCoordIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_of_isLocalization_etale

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
private theorem etale_algebraMap_coordPolynomialRing (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S] :
    (algebraMap (CoordPolynomialRing k m) S).Etale := by
  have hiff : (algebraMap (CoordPolynomialRing k m) S).toAlgebra
      = (inferInstance : Algebra (CoordPolynomialRing k m) S) :=
    Algebra.algebra_ext _ _ fun r => rfl
  show @Algebra.Etale _ _ _ _ (algebraMap (CoordPolynomialRing k m) S).toAlgebra
  rw [hiff]
  infer_instance
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q) :
    IsRegularLocalRing
      (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J)) := by
  classical
  have hIq : etaleChartCoordIdeal k m S J ≤ q := etaleChartCoordIdeal_le k m S J q hJ
  have hq' : (Ideal.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIq)
  let algQuotient : Algebra (CoordPolynomialRing k (m - J.card)) (S ⧸ etaleChartCoordIdeal k m S J) :=
    algebraQuotientCoordIdeal k m S J
  have : Algebra.Etale (CoordPolynomialRing k (m - J.card)) (S ⧸ etaleChartCoordIdeal k m S J) :=
    etale_quotientMk_comp_renameCompl k m J (algebraMap (CoordPolynomialRing k m) S)
      (etale_algebraMap_coordPolynomialRing k m S) (etaleChartCoordIdeal k m S J)
      (map_mvPolynomialCoordIdeal_eq_etaleChartCoordIdeal k m S J).symm
  have h2 : Submonoid.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q.primeCompl
      = (Ideal.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q).primeCompl := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨b, hb, hba⟩ hcon
      refine hb ((Ideal.mem_quotient_iff_mem hIq).mp ?_)
      rw [hba]
      exact hcon
    · intro ha
      exact ⟨a, fun hq => ha ((Ideal.mem_quotient_iff_mem hIq).mpr hq), rfl⟩
  have hloc : IsLocalization
      (Submonoid.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q.primeCompl)
      (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J)) :=
    inferInstanceAs (IsLocalization
      (Algebra.algebraMapSubmonoid (S ⧸ etaleChartCoordIdeal k m S J) q.primeCompl)
      (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J)))
  have : IsLocalization (Ideal.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q).primeCompl
      (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J)) := h2 ▸ hloc
  exact isRegularLocalRing_of_isLocalization_etale k (m - J.card)
    (S ⧸ etaleChartCoordIdeal k m S J)
    (Ideal.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q)
    (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J))
end FunctorialResolution.EmbeddedResolution

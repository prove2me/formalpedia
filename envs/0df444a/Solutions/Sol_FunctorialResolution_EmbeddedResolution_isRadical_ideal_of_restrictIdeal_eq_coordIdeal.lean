-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isRadical_ideal_of_restrictIdeal_eq_coordIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:40:39.24858+00:00
-- url     : https://prove2.me/submissions/19e702ae-9e92-403f-af8f-7b5edd38b626

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PowerContainmentAndOrderLocus
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_etale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_localization_atPrime_etale


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (c : EtaleChart p U n) (Z : X.IdealSheafData) (S : Finset (Fin n))
    (h : restrictIdeal Z U = c.coordIdeal S) :
    (Z.ideal ⟨U, hU⟩).IsRadical := by
  classical
  have hmap : Ideal.map c.coordRingHom (mvPolynomialCoordIdeal k n S) = Z.ideal ⟨U, hU⟩ :=
    c.map_mvPolynomialCoordIdeal_eq_ideal hU Z S h
  have hg := etale_quotientMk_comp_renameCompl k n S c.coordRingHom (c.coordRingHom_etale hU)
    (Z.ideal ⟨U, hU⟩) hmap.symm
  let _ : Algebra (CoordPolynomialRing k (n - S.card)) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :=
    RingHom.toAlgebra
      (((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)).comp c.coordRingHom).comp (renameCompl k n S).toRingHom)
  have : Algebra.Etale (CoordPolynomialRing k (n - S.card)) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) := hg
  have hred : IsReduced (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) := by
    refine isReduced_ofLocalizationMaximal _ ?_
    intro q hq
    have : q.IsPrime := hq.isPrime
    have := isRegularLocalRing_localization_atPrime_etale k (n - S.card)
      (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) q
    have : IsDomain (Localization.AtPrime q) := inferInstance
    exact ⟨fun x hx => hx.eq_zero⟩
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr hred
end FunctorialResolution.EmbeddedResolution

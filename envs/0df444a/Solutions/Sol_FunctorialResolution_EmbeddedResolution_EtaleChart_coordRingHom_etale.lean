-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:18:50.860866+00:00
-- url     : https://prove2.me/submissions/58667551-ad70-4d3b-ac8d-94a7d2445548

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleChart
theorem _root_.solution (c : EtaleChart p U m) (hU : IsAffineOpen U) :
    c.coordRingHom.Etale := by
  have hUaff : IsAffine U.toScheme := hU
  have hEt : AlgebraicGeometry.Etale c.map := c.isEtale
  have hAaff : IsAffine (affineSpaceFin k m) := inferInstance
  have hbeta : IsIso (Scheme.Hom.appTop
      (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom) :=
    inferInstanceAs (IsIso
      ((AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.app ⊤))
  have hResp : RingHom.RespectsIso @RingHom.Etale := RingHom.Etale.respectsIso
  have hmap : RingHom.Etale (Scheme.Hom.appTop c.map).hom :=
    AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine.mp c.isEtale
  exact (hResp.cancel_left_isIso
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv)
      (Scheme.Hom.appTop (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom ≫
        Scheme.Hom.appTop c.map ≫ U.topIso.hom)).mpr
    ((hResp.cancel_left_isIso
        (Scheme.Hom.appTop (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom)
        (Scheme.Hom.appTop c.map ≫ U.topIso.hom)).mpr
      ((hResp.cancel_right_isIso (Scheme.Hom.appTop c.map) U.topIso.hom).mpr hmap))
end EtaleChart
end FunctorialResolution.EmbeddedResolution

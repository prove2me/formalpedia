-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isRegularLocalRing_stalk_affineSpace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:31.723828+00:00
-- url     : https://prove2.me/submissions/8da8c66a-acdd-49d1-b83a-17be3dea37e7

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem isRegularLocalRing_stalk_of_iso_spec {X : Scheme.{u}} (R : Type u) [CommRing R]
    (hreg : ∀ (p : Ideal R) (hp : p.IsPrime),
      _root_.IsRegularLocalRing (@Localization.AtPrime R _ p hp))
    (e : X ≅ Spec (CommRingCat.of R)) (x : X) :
    _root_.IsRegularLocalRing (X.presheaf.stalk x) := by
  let y : PrimeSpectrum R := e.hom.base x
  have hp : y.asIdeal.IsPrime := y.isPrime
  have h1 : _root_.IsRegularLocalRing (@Localization.AtPrime R _ y.asIdeal hp) :=
    hreg y.asIdeal hp
  have h2 : IsLocalization.AtPrime ((Spec.structureSheaf R).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  have e2 : Localization.AtPrime y.asIdeal ≃+* ((Spec.structureSheaf R).presheaf.stalk y) :=
    (IsLocalization.algEquiv y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal)
      ((Spec.structureSheaf R).presheaf.stalk y)).toRingEquiv
  have h3 : _root_.IsRegularLocalRing ((Spec.structureSheaf R).presheaf.stalk y) :=
    IsRegularLocalRing.of_ringEquiv e2
  have h4 : IsIso (e.hom.stalkMap x) := inferInstance
  have e3 : ((Spec.structureSheaf R).presheaf.stalk y) ≃+* (X.presheaf.stalk x) :=
    (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
  exact IsRegularLocalRing.of_ringEquiv e3
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (n : Type u) [Finite n]
    (x : AffineSpace n (Spec (CommRingCat.of k))) :
    _root_.IsRegularLocalRing ((AffineSpace n (Spec (CommRingCat.of k))).presheaf.stalk x) :=
  isRegularLocalRing_stalk_of_iso_spec (MvPolynomial n k)
    (fun p hp => by have := hp; infer_instance)
    (AffineSpace.SpecIso n (CommRingCat.of k)) x
end FunctorialResolution.EmbeddedResolution

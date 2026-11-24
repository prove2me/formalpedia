-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isRegularLocalRing_stalk_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:44.886283+00:00
-- url     : https://prove2.me/submissions/c3a519de-ed43-4ed9-add8-a2d42816de03

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_of_flat_formallyUnramified
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_stalk_affineSpace
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_HasStrictNormalCrossingsWith_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_InStrictNormalCrossingPositionAt_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart

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
private theorem isRegularLocalRing_stalk_of_stalkMap_flat_formallyUnramified {Y Z : Scheme.{u}} (f : Y ⟶ Z) (y : Y)
    (hZ : _root_.IsRegularLocalRing (Z.presheaf.stalk (f.base y)))
    (hflat : (f.stalkMap y).hom.Flat)
    (heft : (f.stalkMap y).hom.EssFiniteType)
    (hfu : (f.stalkMap y).hom.FormallyUnramified) :
    _root_.IsRegularLocalRing (Y.presheaf.stalk y) := by
  have := hZ
  let _ : Algebra (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    (f.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
  have : Module.Flat (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hflat
  have : Algebra.EssFiniteType (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := heft
  have : Algebra.FormallyUnramified (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hfu
  have : IsNoetherianRing (Y.presheaf.stalk y) :=
    Algebra.EssFiniteType.isNoetherianRing
      (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)
  exact isRegularLocalRing_of_flat_formallyUnramified
    (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)
private theorem isRegularLocalRing_stalk_of_opens {X : Scheme.{u}} (U : X.Opens) (y : U)
    (h : _root_.IsRegularLocalRing (U.toScheme.presheaf.stalk y)) :
    _root_.IsRegularLocalRing (X.presheaf.stalk y.1) := by
  have := h
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso y).commRingCatIsoToRingEquiv
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    _root_.IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, m, hxU, -, ⟨c⟩⟩ := exists_etaleChart p x
  have := c.isEtale
  have hreg : _root_.IsRegularLocalRing
      ((affineSpaceFin k m).presheaf.stalk (c.map.base (⟨x, hxU⟩ : U))) :=
    isRegularLocalRing_stalk_affineSpace k (ULift.{u} (Fin m)) _
  have h2 : _root_.IsRegularLocalRing (U.toScheme.presheaf.stalk (⟨x, hxU⟩ : U)) :=
    isRegularLocalRing_stalk_of_stalkMap_flat_formallyUnramified c.map (⟨x, hxU⟩ : U) hreg
      (AlgebraicGeometry.Flat.stalkMap c.map (⟨x, hxU⟩ : U))
      (AlgebraicGeometry.LocallyOfFiniteType.stalkMap c.map (⟨x, hxU⟩ : U))
      (AlgebraicGeometry.FormallyUnramified.stalkMap c.map (⟨x, hxU⟩ : U))
  exact isRegularLocalRing_stalk_of_opens U (⟨x, hxU⟩ : U) h2
end FunctorialResolution.EmbeddedResolution

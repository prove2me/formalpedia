-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.ringKrullDim_stalk_eq_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:50:09.382811+00:00
-- url     : https://prove2.me/submissions/46483fad-eae3-4081-937c-76081324c2fa

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_AffineSpaceJacobson
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StalkKrullDimension
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ringKrullDim_eq_of_flat_formallyUnramified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {Y W : Scheme.{u}} (f : Y ⟶ W)
    [AlgebraicGeometry.Etale f] (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    [_root_.IsRegularLocalRing (W.presheaf.stalk (f.base y))] :
    ringKrullDim (Y.presheaf.stalk y) = ringKrullDim (W.presheaf.stalk (f.base y)) := by
  have hft : (f.stalkMap y).hom.EssFiniteType :=
    AlgebraicGeometry.LocallyOfFiniteType.stalkMap f y
  have hfu : (f.stalkMap y).hom.FormallyUnramified :=
    AlgebraicGeometry.FormallyUnramified.stalkMap f y
  let algStalk : Algebra (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    (f.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
  have : Module.Flat (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    AlgebraicGeometry.Flat.stalkMap f y
  have : Algebra.EssFiniteType (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hft
  have : Algebra.FormallyUnramified (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hfu
  exact FunctorialResolution.EmbeddedResolution.ringKrullDim_eq_of_flat_formallyUnramified
    (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)
end FunctorialResolution.EmbeddedResolution

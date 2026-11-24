-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:51.079069+00:00
-- url     : https://prove2.me/submissions/44d5f9f3-4f05-47fa-9cab-de8680a04de7

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_mono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
private theorem map_germ_le_stalkIdeal {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (U : {U : X.affineOpens // x ∈ U.1.1}) :
    Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (I.ideal U.1) ≤ stalkIdeal I x :=
  le_iSup (fun V : {V : X.affineOpens // x ∈ V.1.1} =>
    Ideal.map (X.presheaf.germ V.1.1 x V.2).hom (I.ideal V.1)) U
private theorem stalkIdeal_sup_le {X : Scheme.{u}} (I J : X.IdealSheafData) (x : X) :
    stalkIdeal (I ⊔ J) x ≤ stalkIdeal I x ⊔ stalkIdeal J x := by
  show (⨆ U : {U : X.affineOpens // x ∈ U.1.1},
      Ideal.map (X.presheaf.germ U.1.1 x U.2).hom ((I ⊔ J).ideal U.1)) ≤
      stalkIdeal I x ⊔ stalkIdeal J x
  refine iSup_le fun U => ?_
  have h1 : (I ⊔ J).ideal U.1 = I.ideal U.1 ⊔ J.ideal U.1 := rfl
  rw [h1, Ideal.map_sup]
  exact sup_le (le_sup_of_le_left (map_germ_le_stalkIdeal I x U))
    (le_sup_of_le_right (map_germ_le_stalkIdeal J x U))
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (I J : X.IdealSheafData) (x : X) :
    stalkIdeal (I ⊔ J) x = stalkIdeal I x ⊔ stalkIdeal J x :=
  le_antisymm (stalkIdeal_sup_le I J x)
    (sup_le (stalkIdeal_mono le_sup_left x) (stalkIdeal_mono le_sup_right x))
end FunctorialResolution.EmbeddedResolution

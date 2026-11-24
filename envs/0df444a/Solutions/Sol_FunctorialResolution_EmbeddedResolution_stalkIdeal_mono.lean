-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:06.774257+00:00
-- url     : https://prove2.me/submissions/601fffe0-21f8-46fd-b355-3f7e1cc1c4e7

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {I J : X.IdealSheafData} (h : I ≤ J) (x : X) :
    stalkIdeal I x ≤ stalkIdeal J x := by
  show (⨆ U : {U : X.affineOpens // x ∈ U.1.1},
        Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (I.ideal U.1)) ≤
      ⨆ U : {U : X.affineOpens // x ∈ U.1.1},
        Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (J.ideal U.1)
  exact iSup_mono fun U => Ideal.map_mono (h U.1)
end FunctorialResolution.EmbeddedResolution

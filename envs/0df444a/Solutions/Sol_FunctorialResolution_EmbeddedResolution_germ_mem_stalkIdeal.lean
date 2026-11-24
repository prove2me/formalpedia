-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.germ_mem_stalkIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:33.242062+00:00
-- url     : https://prove2.me/submissions/4cdc33ad-e075-48db-bba8-10ae33a3e74c

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
theorem _root_.solution (I : X.IdealSheafData) (x : X) (U : X.affineOpens) (hx : x ∈ U.1)
    {s : Γ(X, U.1)} (hs : s ∈ I.ideal U) :
    (X.presheaf.germ U.1 x hx).hom s ∈ stalkIdeal I x := by
  have h : Ideal.map (X.presheaf.germ U.1 x hx).hom (I.ideal U) ≤ stalkIdeal I x :=
    le_iSup (fun V : {V : X.affineOpens // x ∈ V.1.1} =>
      Ideal.map (X.presheaf.germ V.1.1 x V.2).hom (I.ideal V.1)) ⟨U, hx⟩
  exact SetLike.le_def.mp h (Ideal.mem_map_of_mem _ hs)
end FunctorialResolution.EmbeddedResolution

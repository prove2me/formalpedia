-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:06.750727+00:00
-- url     : https://prove2.me/submissions/071630e8-cbe0-43e6-b7ea-f712474c9015

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_map_germ
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineOpens_mem


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
theorem _root_.solution (I J : X.IdealSheafData) (x : X) :
    stalkIdeal (I * J) x = stalkIdeal I x * stalkIdeal J x := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have hmul : (I * J).ideal U = I.ideal U * J.ideal U :=
    congrFun (Scheme.IdealSheafData.ideal_mul ..) U
  rw [stalkIdeal_eq_map_germ (I * J) x U hxU, stalkIdeal_eq_map_germ I x U hxU,
    stalkIdeal_eq_map_germ J x U hxU, hmul, Ideal.map_mul]
end FunctorialResolution.EmbeddedResolution

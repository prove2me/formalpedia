-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf.eq_of_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:00:25.054917+00:00
-- url     : https://prove2.me/submissions/01358d17-3b91-4678-ac72-6d8fca9ede1f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IdealSheafFlatComapInjective
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_FlatDescentIdealSheaf_le_of_comap_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf
variable {W Y : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf
theorem _root_.solution (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.Surjective g] (I J : Y.IdealSheafData)
    (h : I.comap g = J.comap g) : I = J :=
  le_antisymm (le_of_comap_le g I J (le_of_eq h)) (le_of_comap_le g J I (le_of_eq h.symm))
end FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf

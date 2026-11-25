-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isDerivBalanced_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:22:03.106999+00:00
-- url     : https://prove2.me/submissions/3fe895dd-35a5-477b-ae54-b722859f70a8

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero



set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (I : X.IdealSheafData) : IsDerivBalanced k p I 1 := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  have h : derivIdealSheafIterate k p 0 I = I := derivIdealSheafIterate_zero k p I
  exact le_of_eq (by rw [h, Nat.sub_zero])
end FunctorialResolution.EmbeddedResolution

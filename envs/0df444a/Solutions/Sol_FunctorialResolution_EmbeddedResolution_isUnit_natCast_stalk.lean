-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isUnit_natCast_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:24:13.214713+00:00
-- url     : https://prove2.me/submissions/504c53a7-5be9-488b-958a-5122ad7a95e8

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) {n : ℕ} (hn : 1 ≤ n) :
    IsUnit ((n : ℕ) : X.presheaf.stalk x) := by
  have hne : ((n : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk : IsUnit ((n : ℕ) : k) := IsUnit.mk0 _ hne
  have h := hk.map (stalkAlgebraMap k p x)
  rwa [map_natCast] at h
end FunctorialResolution.EmbeddedResolution

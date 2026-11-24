-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdealSheaf_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:17:29.881697+00:00
-- url     : https://prove2.me/submissions/696d209b-6757-4e8a-905d-7b8f6cc2c84f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_le_derivIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap


attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    Monotone (derivIdealSheaf k p) := by
  intro I J h
  have key : ∀ U : X.affineOpens,
      (derivIdealSheaf k p I).ideal U ≤ (derivIdealSheaf k p J).ideal U := by
    intro U
    have hU : I.ideal U ≤ J.ideal U := h U
    rw [derivIdealSheaf_ideal, derivIdealSheaf_ideal]
    exact @derivIdeal_le_derivIdeal k _ _ _ (sectionsAlgebra k p U.1) _ _ hU
  exact key
end FunctorialResolution.EmbeddedResolution

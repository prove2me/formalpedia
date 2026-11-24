-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:19:53.788802+00:00
-- url     : https://prove2.me/submissions/f9afb473-ee61-4b4f-82ce-f1bc0e74dabe

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_succ
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_zero
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
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (r : ℕ)
    (I : X.IdealSheafData) (U : X.affineOpens) :
    (derivIdealSheafIterate k p r I).ideal U =
      @derivIdealIterate k _ _ _ (sectionsAlgebra k p U.1) r (I.ideal U) := by
  induction r with
  | zero =>
      rw [derivIdealSheafIterate_zero,
        @derivIdealIterate_zero k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U)]
  | succ n ih =>
      rw [derivIdealSheafIterate_succ, derivIdealSheaf_ideal, ih,
        @derivIdealIterate_succ k _ _ _ (sectionsAlgebra k p U.1) n (I.ideal U)]
end FunctorialResolution.EmbeddedResolution

-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.logDerivIdealSheafIterate_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:24:08.299916+00:00
-- url     : https://prove2.me/submissions/ef60c796-56e2-4fb5-8553-9acf3c5c7180

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheaf
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealSheaf_mono
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealSheafIterate_succ
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


attribute [local simp] FunctorialResolution.EmbeddedResolution.logDerivIdealSheafIterate_zero

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) (r : ℕ) :
    Monotone (logDerivIdealSheafIterate k p P r) := by
  induction r with
  | zero =>
      intro I J h
      rw [logDerivIdealSheafIterate_zero, logDerivIdealSheafIterate_zero]
      exact h
  | succ r ih =>
      intro I J h
      rw [logDerivIdealSheafIterate_succ, logDerivIdealSheafIterate_succ]
      exact logDerivIdealSheaf_mono k p P (ih h)
end FunctorialResolution.EmbeddedResolution

-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.logDerivIdealSheafIterate_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:23:51.456904+00:00
-- url     : https://prove2.me/submissions/2a9588fd-727f-4047-b194-0a380a124b80

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheaf
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
    (P : X.IdealSheafData) (r s : ℕ) (I : X.IdealSheafData) :
    logDerivIdealSheafIterate k p P (r + s) I =
      logDerivIdealSheafIterate k p P r (logDerivIdealSheafIterate k p P s I) := by
  induction r with
  | zero =>
      rw [Nat.zero_add, logDerivIdealSheafIterate_zero]
  | succ r ih =>
      have hrs : r + 1 + s = (r + s) + 1 := by omega
      rw [hrs, logDerivIdealSheafIterate_succ, logDerivIdealSheafIterate_succ, ih]
end FunctorialResolution.EmbeddedResolution

-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.le_derivIdealSheafIterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:18:59.226874+00:00
-- url     : https://prove2.me/submissions/39bd36f2-6556-437d-86f6-989e99a464f0

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdealSheaf
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_succ

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
theorem _root_.solution (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (r : ℕ) (I : X.IdealSheafData) :
    I ≤ derivIdealSheafIterate k p r I := by
  induction r with
  | zero => exact le_rfl
  | succ n ih =>
    rw [derivIdealSheafIterate_succ]
    exact le_trans ih (le_derivIdealSheaf k p (derivIdealSheafIterate k p n I))
end FunctorialResolution.EmbeddedResolution

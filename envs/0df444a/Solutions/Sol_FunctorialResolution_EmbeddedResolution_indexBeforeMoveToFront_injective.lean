-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.indexBeforeMoveToFront_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:49:03.767122+00:00
-- url     : https://prove2.me/submissions/3330b5c8-a543-4fa0-976e-2d7e331fdb58

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DivisorReduction_StrictNormalCrossingsMoveToFront

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {α : Type*}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (j : ℕ) : Function.Injective (indexBeforeMoveToFront j) := by
  intro a b hab
  cases a with
  | zero =>
    cases b with
    | zero => rfl
    | succ i =>
      exfalso
      simp only [indexBeforeMoveToFront] at hab
      split_ifs at hab <;> omega
  | succ i =>
    cases b with
    | zero =>
      exfalso
      simp only [indexBeforeMoveToFront] at hab
      split_ifs at hab <;> omega
    | succ i' =>
      simp only [indexBeforeMoveToFront] at hab
      split_ifs at hab <;> omega
end FunctorialResolution.EmbeddedResolution

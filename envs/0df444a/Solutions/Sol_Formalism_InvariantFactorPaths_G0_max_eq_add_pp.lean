-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G0.max_eq_add_pp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:44:34.963449+00:00
-- url     : https://prove2.me/submissions/343ab9a2-927c-467d-bee1-e7ccd4d40b18

import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ElementarySymmetricExpBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_LePowOddOfFloorLogbLe
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_ElementarySymmetricExpBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Pointwise
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G0
open Formalism.G0
namespace Formalism.InvariantFactorPaths.G0
theorem _root_.solution (x y : ℝ) : max x y = y + pp (x - y) := by
  unfold pp
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (by linarith : x - y ≤ 0)]
    ring
  · rw [max_eq_left h, max_eq_left (by linarith : 0 ≤ x - y)]
    ring
end Formalism.InvariantFactorPaths.G0

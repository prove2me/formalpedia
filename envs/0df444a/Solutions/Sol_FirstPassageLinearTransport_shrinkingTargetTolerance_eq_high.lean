-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingTargetTolerance_eq_high
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:45.684798+00:00
-- url     : https://prove2.me/submissions/b5f03afe-56a9-401a-9cd3-80815ea80ef5

import Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : ShrinkingBarrierRunData) {M S q : ℕ} (hSq : S < q) :
    shrinkingTargetTolerance P M S q =
      shrinkingHighTolerance P M (q - 1) := by
  unfold shrinkingTargetTolerance
  rw [if_pos (by omega)]
end FirstPassageLinearTransport

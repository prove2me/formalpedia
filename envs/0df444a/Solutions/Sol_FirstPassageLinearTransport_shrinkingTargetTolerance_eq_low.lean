-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingTargetTolerance_eq_low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:54.703385+00:00
-- url     : https://prove2.me/submissions/bf8853fa-fe02-407f-9eaa-5069b9d687b7

import Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : ShrinkingBarrierRunData) {M S q : ℕ}
    (hq1 : 1 ≤ q) (hqS : q ≤ S) :
    shrinkingTargetTolerance P M S q = P.etaLo := by
  unfold shrinkingTargetTolerance
  rw [if_neg (by omega)]
end FirstPassageLinearTransport

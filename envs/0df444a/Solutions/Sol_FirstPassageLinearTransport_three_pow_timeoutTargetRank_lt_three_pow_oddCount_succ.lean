-- Prove2me | solution 1 for FirstPassageLinearTransport.three_pow_timeoutTargetRank_lt_three_pow_oddCount_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:03:59.11265+00:00
-- url     : https://prove2.me/submissions/a2ff29da-0685-4fea-bccc-34599df8cb15

import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Theorems.Thm_FirstPassageLinearTransport_orbit_timeout_lt_three_pow_succ

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Topology
namespace FirstPassageLinearTransport
theorem _root_.solution
    {K₀ : ℝ} {L m x : ℕ}
    (hx : x ∈ dyadicShell m)
    (htimeout : LowStageTimeout K₀ L m x) :
    2 ^ timeoutTargetRank K₀ L m < 3 ^ (oddCount x m + 1) := by
  exact lt_trans (htimeout ⟨m, by omega⟩)
    (orbit_timeout_lt_three_pow_succ hx)
end FirstPassageLinearTransport

-- Prove2me | solution 1 for FirstPassageLinearTransport.twoRegimeHorizon_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:45:25.819884+00:00
-- url     : https://prove2.me/submissions/be4e5e16-43f2-4156-b723-04b81c9bc109

import Definitions.Def_FirstPassageLinearTransport_TwoRegimeRun
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (rHi rLo : ℚ) (S M : ℕ) :
    (M : ℝ) / (1 - (rHi : ℝ)) +
        (S : ℝ) / (1 - (rLo : ℝ)) ≤
      (twoRegimeHorizon rHi rLo S M : ℝ) := by
  exact Nat.le_ceil _
end FirstPassageLinearTransport

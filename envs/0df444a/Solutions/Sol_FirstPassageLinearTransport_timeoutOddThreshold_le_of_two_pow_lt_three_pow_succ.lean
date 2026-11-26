-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutOddThreshold_le_of_two_pow_lt_three_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:06:43.564853+00:00
-- url     : https://prove2.me/submissions/fd3b4890-f232-4409-908d-e1ff5e0a42e8

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {q s : ℕ} (h : 2 ^ q < 3 ^ (s + 1)) :
    timeoutOddThreshold q ≤ s := by
  exact Nat.find_min' (exists_two_pow_lt_three_pow_succ q) h
end FirstPassageLinearTransport

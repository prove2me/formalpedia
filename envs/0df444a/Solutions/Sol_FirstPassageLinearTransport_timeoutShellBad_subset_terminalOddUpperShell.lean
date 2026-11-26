-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutShellBad_subset_terminalOddUpperShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:07:37.541679+00:00
-- url     : https://prove2.me/submissions/38989949-990a-4133-915c-108779064a8e

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_timeoutOddThreshold_le_of_two_pow_lt_three_pow_succ
import Theorems.Thm_FirstPassageLinearTransport_three_pow_timeoutTargetRank_lt_three_pow_oddCount_succ


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (K₀ : ℝ) (L m : ℕ) :
    timeoutShellBad K₀ L m ⊆
      terminalOddUpperShell m
        (timeoutOddThreshold (timeoutTargetRank K₀ L m)) := by
  classical
  intro x hx
  rw [timeoutShellBad, Finset.mem_filter] at hx
  rw [terminalOddUpperShell, Finset.mem_filter]
  refine ⟨hx.1, ?_⟩
  exact timeoutOddThreshold_le_of_two_pow_lt_three_pow_succ
    (three_pow_timeoutTargetRank_lt_three_pow_oddCount_succ hx.1 hx.2)
end FirstPassageLinearTransport

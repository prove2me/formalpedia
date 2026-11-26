-- Prove2me | solution 1 for FirstPassageLinearTransport.card_timeoutShellBad_le_binomialUpperTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:56.9308+00:00
-- url     : https://prove2.me/submissions/6745bd4f-56e3-48c3-92ee-082038b99d8f

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_card_terminalOddUpperShell
import Theorems.Thm_FirstPassageLinearTransport_timeoutShellBad_subset_terminalOddUpperShell

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {K₀ : ℝ} {L m : ℕ}
    (hk : timeoutOddThreshold (timeoutTargetRank K₀ L m) ≤ m) :
    (timeoutShellBad K₀ L m).card ≤
      binomialUpperTail m
        (timeoutOddThreshold (timeoutTargetRank K₀ L m)) := by
  calc
    (timeoutShellBad K₀ L m).card ≤
        (terminalOddUpperShell m
          (timeoutOddThreshold (timeoutTargetRank K₀ L m))).card :=
      Finset.card_le_card (timeoutShellBad_subset_terminalOddUpperShell K₀ L m)
    _ = binomialUpperTail m
          (timeoutOddThreshold (timeoutTargetRank K₀ L m)) :=
      card_terminalOddUpperShell hk
end FirstPassageLinearTransport

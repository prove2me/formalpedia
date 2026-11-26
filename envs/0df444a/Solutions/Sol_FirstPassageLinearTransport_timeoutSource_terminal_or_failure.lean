-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutSource_terminal_or_failure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:14:12.464313+00:00
-- url     : https://prove2.me/submissions/6ab83fbf-0088-47f8-9aaf-9ae2793b6fcb

import Definitions.Def_FirstPassageLinearTransport_TimeoutEnvelope
import Definitions.Def_FirstPassageLinearTransport_TimeoutExecution
import Theorems.Thm_FirstPassageLinearTransport_timeoutRun_terminal_or_failure
import Theorems.Thm_FirstPassageLinearTransport_shellBad_initialWindowGood


set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) (K₀ : ℝ)
    {M L S n : ℕ}
    (hSM : S ≤ M) (hM0 : P.pHi.M0 ≤ M)
    (hL2 : 2 ≤ L) (hLS : L ≤ S)
    (hHiStartup : P.pHi.M0 ≤ L)
    (hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank K₀ L (p - 1))
    (hnextParent : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank K₀ L (p - 1) < p - 1)
    (hq0M : rationalTargetRank P.rHi M ≤ M - 1)
    (hnShell : n ∈ dyadicShell M) :
    HasTimeoutTerminalLanding P K₀ L M S n ∨
      n ∈ timeoutSeparatedFailureEnvelope P K₀ M L S := by
  classical
  by_cases hnGood : n ∈ initialWindowGood (timeoutHighTolerance P M M)
  · let firstRun : TimeoutRecertificationRun P K₀ L M S n
        (stageLength (timeoutHighSetup P M M) n)
        (rationalTargetRank P.rHi M) :=
      TimeoutRecertificationRun.first hSM hM0 hnShell hnGood
    exact timeoutRun_terminal_or_failure P K₀ hL2 hLS hHiStartup
      hnextPos hnextParent hq0M firstRun
  · exact Or.inr (by
      unfold timeoutSeparatedFailureEnvelope
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      have hnBad : n ∈ shellBad
          (initialWindowGood (timeoutHighTolerance P M M)) M :=
        Finset.mem_filter.mpr ⟨hnShell, hnGood⟩
      rw [shellBad_initialWindowGood] at hnBad
      exact hnBad)
end FirstPassageLinearTransport

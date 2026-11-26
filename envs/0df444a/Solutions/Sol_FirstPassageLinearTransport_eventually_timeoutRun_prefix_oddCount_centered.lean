-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_timeoutRun_prefix_oddCount_centered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:22.97278+00:00
-- url     : https://prove2.me/submissions/bcfda020-6bf5-45b8-afd6-845ee5b8744b

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_reverseProduct_antitone
import Theorems.Thm_FirstPassageLinearTransport_oddCount_centered_of_reverseProduct_half
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_prefix_log_deviation_le_sqrt
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_source_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_reverseProduct_half
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {n elapsed q : ℕ},
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
        (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
        n elapsed q →
      ∀ j : ℕ, j ≤ elapsed →
        |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
          (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch *
              Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) +
            Real.log 2) / Real.log 3 := by
  filter_upwards [eventually_timeoutRun_reverseProduct_half P hbuffer,
      eventually_timeoutRun_prefix_log_deviation_le_sqrt
        P.run.toTimeoutHigh P.Cswitch_pos.le]
    with M hreverse htube
  intro n elapsed q hrun j hj
  have hnShell := hrun.source_mem_dyadicShell
  have hn : 0 < n := by
    have hnLower := (mem_dyadicShell.mp hnShell).1
    have hpow : 0 < 2 ^ M := by positivity
    omega
  have hfinal := hreverse hrun
  have hprefixMono := reverseProduct_antitone hn hj
  have hprefix : (1 / 2 : ℚ) ≤ reverseProduct n j :=
    hfinal.trans hprefixMono
  exact oddCount_centered_of_reverseProduct_half hn hprefix
    (htube hrun j hj)
end FirstPassageLinearTransport

-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_timeoutRun_prefix_raw_log_deviation_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:56.755908+00:00
-- url     : https://prove2.me/submissions/6c004245-86c7-45bc-9e85-bfe07d6a6ad9

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_rawOddDeviationCoefficient_nonneg
import Theorems.Thm_FirstPassageLinearTransport_rawPrefix_log_deviation_le
import Theorems.Thm_FirstPassageLinearTransport_one_le_timeoutProfileRoot
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_prefix_log_deviation_le_sqrt
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_prefix_oddCount_centered
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_source_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutHighFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimeSupportConstant_pos
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFeasibleTimes
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_timeoutFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_timeoutHighFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons


attribute [local simp] FirstPassageLinearTransport.shortcutFirstPassageTime_self
attribute [local simp] FirstPassageLinearTransport.rawFirstPassageTime_self

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
      ∀ i : ℕ, i ≤ rawTime n elapsed →
        |rawLogDeviation n i| ≤
          timeoutRawTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  filter_upwards [eventually_timeoutRun_prefix_log_deviation_le_sqrt
        P.run.toTimeoutHigh P.Cswitch_pos.le,
      eventually_timeoutRun_prefix_oddCount_centered P hbuffer,
      eventually_ge_atTop (1 : ℕ)]
    with M hshortcut hodd hM
  intro n elapsed q hrun i hi
  let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  let E := timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch * root
  let F := (E + Real.log 2) / Real.log 3
  have hraw := rawPrefix_log_deviation_le
    (n := n) (k := elapsed) (E := E) (F := F)
    (by
      have hnShell := hrun.source_mem_dyadicShell
      have hnLower := (mem_dyadicShell.mp hnShell).1
      have hpow : 0 < 2 ^ M := by positivity
      omega)
    (fun j hj => by simpa [E, root] using hshortcut hrun j hj)
    (fun j hj => by simpa [F, E, root] using hodd hrun j hj)
    i hi
  have hroot1 : 1 ≤ root := by
    simpa [root] using one_le_timeoutProfileRoot hM
  have hlogTwoLe : Real.log 2 ≤ 1 :=
    (Real.log_two_lt_d9.trans (by norm_num)).le
  have hcoef0 := rawOddDeviationCoefficient_nonneg
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have htime0 : 0 < timeoutTimeSupportConstant
      P.run.toTimeoutHigh P.Cswitch :=
    timeoutTimeSupportConstant_pos _ _
  have hroot0 : 0 ≤ root := by linarith
  have hnum : E + Real.log 2 ≤
      (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
        root := by
    dsimp [E]
    nlinarith
  have hFscale : F ≤
      ((timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) /
          Real.log 3) * root := by
    calc
      F = (E + Real.log 2) / Real.log 3 := rfl
      _ ≤ ((timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
          root) / Real.log 3 :=
        (div_le_div_iff_of_pos_right hlog3).2 hnum
      _ = ((timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) /
          Real.log 3) * root := by ring
  have hcoefF := mul_le_mul_of_nonneg_left hFscale hcoef0
  dsimp [timeoutRawTrajectorySupportConstant]
  dsimp [E, F, root] at hraw ⊢
  nlinarith [mul_nonneg htime0.le hroot0]
end FirstPassageLinearTransport

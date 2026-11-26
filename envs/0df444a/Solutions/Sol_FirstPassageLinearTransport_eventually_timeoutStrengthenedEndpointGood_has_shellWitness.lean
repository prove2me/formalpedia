-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_timeoutStrengthenedEndpointGood_has_shellWitness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:35:23.162973+00:00
-- url     : https://prove2.me/submissions/0b354c31-d3fb-4ca2-80dd-3a078e1e7911

import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Definitions.Def_FirstPassageLinearTransport_PolylogTarget
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointWitness
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_endpoint_lt_start
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_shortcut_raw_le_relative_height
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_eventually_movingExponent_pos_of_sharp
import Theorems.Thm_FirstPassageLinearTransport_eventually_movingTerminalRank_lt_shrinkingSwitchRank
import Theorems.Thm_FirstPassageLinearTransport_eventually_shrinkingSwitchRank_envelope_le_shellMargin
import Theorems.Thm_FirstPassageLinearTransport_eventually_shrinkingSwitchRank_lt_source
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_completed_centered
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_completed_oddCount_centered_le_sqrt
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_completed_prefix_log_deviation_le_sqrt
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_completed_rawTime_centered
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_completed_raw_log_deviation_le_sqrt
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_elapsed_add_switch_lt_shellClock
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_prefix_log_deviation_le_sqrt
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_prefix_oddCount_centered_le_sqrt
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_prefix_raw_log_deviation_le_sqrt
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_rawTime_centered
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutTargetRank_admissible
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
import Theorems.Thm_FirstPassageLinearTransport_orbit_add
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rationalTargetRank_lt_parent
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_le_two_mul_of_shortcut_prefix_le
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_rawTime_eq_orbit
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shellPolylogTarget_le_natLog
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingTerminalRank_atTop_of_sharp
import Theorems.Thm_FirstPassageLinearTransport_timeoutOddTrajectorySupportConstant_le_completed
import Theorems.Thm_FirstPassageLinearTransport_timeoutRawTrajectorySupportConstant_le_completed
import Theorems.Thm_FirstPassageLinearTransport_timeoutSource_terminal_or_failure
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimeSupportConstant_pos
import Theorems.Thm_FirstPassageLinearTransport_timeout_orbit_two_pow
import Theorems.Thm_FirstPassageLinearTransport_two_pow_movingTerminalRank_lt
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
attribute [local simp] FirstPassageLinearTransport.rawFirstPassageTime_self
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcutFirstPassageTime_self
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons


section
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
private theorem timeout_fixedPolylogTargetConstant_mono
    {a b : ℝ} (hab : a ≤ b) :
    fixedPolylogTargetConstant a ≤ fixedPolylogTargetConstant b := by
  unfold fixedPolylogTargetConstant
  have hbase : 1 ≤ 1 / Real.log 2 + 2 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hinv : 0 < 1 / Real.log 2 := by positivity
    linarith
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hbase hab) (by norm_num)
end
end FirstPassageLinearTransport
end

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A R : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax)
    (hR : ∀ᶠ M : ℕ in atTop, 4 ≤ R M) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      n ∈ dyadicShell M →
      n ∈ timeoutStrengthenedEndpointGood P A R M →
      ∃ k ell : ℕ,
        (k : ℝ) < c * (M : ℝ) * Real.log 2 ∧
        |driftGap * (k : ℝ) - (M : ℝ)| ≤
          2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) ∧
        |(2 * driftGap / 3) * (ell : ℝ) - (M : ℝ)| ≤
          timeoutCompletedRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) ∧
        (∀ j : ℕ, j ≤ k →
          |shortcutLogDeviation n j| ≤
            2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch *
              Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))) ∧
        (∀ j : ℕ, j ≤ k →
          |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
            timeoutCompletedOddTrajectorySupportConstant
                P.run.toTimeoutHigh P.Cswitch *
              Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))) ∧
        (∀ i : ℕ, i ≤ ell →
          |rawLogDeviation n i| ≤
            timeoutCompletedRawTrajectorySupportConstant
                P.run.toTimeoutHigh P.Cswitch *
              Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))) ∧
        ell = rawTime n k ∧
        rawOrbit ell n = orbit k n ∧
        (orbit k n : ℝ) <
          fixedPolylogTargetConstant Amax * (Real.log n) ^ (A M) ∧
        (∀ j : ℕ, j ≤ k →
          (orbit j n : ℝ) ≤ (n : ℝ) * R M / 2) ∧
        (∀ i : ℕ, i ≤ ell →
          (rawOrbit i n : ℝ) ≤ (n : ℝ) * R M) := by
  have hTerminalT := tendsto_movingTerminalRank_atTop_of_sharp hbuffer
  have hL2 := (tendsto_atTop.1 hTerminalT) 2
  have hHiStartup := (tendsto_atTop.1 hTerminalT) P.run.pHi.M0
  have hLS := eventually_movingTerminalRank_lt_shrinkingSwitchRank
    P.Amax_pos.le P.terminal_below_switch hUpper
  have hSwitch := eventually_shrinkingSwitchRank_lt_source P.Cswitch_pos.le
  have hClock := eventually_timeoutRun_elapsed_add_switch_lt_shellClock P
  have hCentered := eventually_timeoutRun_completed_centered
    (K₀ := P.K₀) P.run.toTimeoutHigh P.Cswitch_pos.le
  have hRawCentered := eventually_timeoutRun_rawTime_centered P hbuffer
  have hRawCompleted :=
    eventually_timeoutRun_completed_rawTime_centered P hbuffer
  have hShortcutTube := eventually_timeoutRun_prefix_log_deviation_le_sqrt
    (K₀ := P.K₀) P.run.toTimeoutHigh P.Cswitch_pos.le
  have hShortcutCompleted :=
    eventually_timeoutRun_completed_prefix_log_deviation_le_sqrt
      (K₀ := P.K₀) P.run.toTimeoutHigh P.Cswitch_pos.le
  have hOddTube :=
    eventually_timeoutRun_prefix_oddCount_centered_le_sqrt P hbuffer
  have hOddCompleted :=
    eventually_timeoutRun_completed_oddCount_centered_le_sqrt P hbuffer
  have hRawTube :=
    eventually_timeoutRun_prefix_raw_log_deviation_le_sqrt P hbuffer
  have hRawTrajectoryCompleted :=
    eventually_timeoutRun_completed_raw_log_deviation_le_sqrt P hbuffer
  have hUnitMargin := eventually_shrinkingSwitchRank_envelope_le_shellMargin
    P.Cswitch_pos.le (show (0 : ℝ) ≤ 1 by norm_num)
      (show (0 : ℝ) < 1 by norm_num)
  have hA0 := eventually_movingExponent_pos_of_sharp hbuffer
  have hTimeoutAdmBase := eventually_timeoutTargetRank_admissible
    (show 0 < P.K₀ by linarith [P.K₀_gt_six])
  have hTimeoutAdm := hTerminalT.eventually hTimeoutAdmBase
  filter_upwards [hL2, hHiStartup, hLS, hSwitch, hClock, hCentered,
      hRawCentered, hRawCompleted, hShortcutTube, hShortcutCompleted,
      hOddTube, hOddCompleted, hRawTube, hRawTrajectoryCompleted,
      hUnitMargin, hA0, hUpper, hTimeoutAdm, hR,
      eventually_ge_atTop P.run.pHi.M0, eventually_ge_atTop (3 : ℕ)]
    with M hL2 hHiStartup hLS hSwitch hClock hCentered hRawCentered
      hRawCompleted hShortcutTube hShortcutCompleted hOddTube hOddCompleted
      hRawTube hRawTrajectoryCompleted hUnitMargin hA0 hUpper hTimeoutAdm hR
      hM0 hM3
  intro n hnShell hnGood
  let L := movingTerminalRank A M
  let S := shrinkingSwitchRank P.Cswitch M
  have hSM : S ≤ M := by dsimp [S]; exact hSwitch.le
  have hL2' : 2 ≤ L := by simpa [L] using hL2
  have hLS' : L ≤ S := by dsimp [L, S]; exact hLS.le
  have hHiStartup' : P.run.pHi.M0 ≤ L := by simpa [L] using hHiStartup
  have hLowMargin : 2 * S ≤ M := by
    have hUnitMargin' : (S : ℝ) * (1 + 1) ≤ (1 : ℝ) * (M : ℝ) := by
      simpa [S] using hUnitMargin
    norm_num at hUnitMargin'
    have hSMul : S * 2 ≤ M := by exact_mod_cast hUnitMargin'
    omega
  have hq0M : rationalTargetRank P.run.rHi M ≤ M - 1 := by
    have hlt := rationalTargetRank_lt_parent
      (by exact_mod_cast P.run.pHi.r_pos.le)
      (by exact_mod_cast P.run.pHi.r_lt_one) (by omega : 0 < M)
    omega
  have hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank P.K₀ L (p - 1) := by
    intro p hp
    exact (hTimeoutAdm (p - 1) (by
      have hpI := Finset.mem_Icc.mp hp
      omega)).1
  have hnextParent : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank P.K₀ L (p - 1) < p - 1 := by
    intro p hp
    exact (hTimeoutAdm (p - 1) (by
      have hpI := Finset.mem_Icc.mp hp
      omega)).2
  have hnNotStrengthened : n ∉ timeoutStrengthenedFailureEnvelope
      P.run.toTimeoutHigh P.K₀ M L S (R M) := by
    simpa [timeoutStrengthenedEndpointGood, L, S] using hnGood
  have hnNotFailure : n ∉
      timeoutSeparatedFailureEnvelope P.run.toTimeoutHigh P.K₀ M L S := by
    intro hn
    exact hnNotStrengthened (by
      unfold timeoutStrengthenedFailureEnvelope
      exact Finset.mem_union_left _ hn)
  have hnMax : n ∉ shellMultiplicativeHit M (R M / 4) := by
    intro hn
    exact hnNotStrengthened (by
      unfold timeoutStrengthenedFailureEnvelope
      exact Finset.mem_union_right _ hn)
  rcases timeoutSource_terminal_or_failure P.run.toTimeoutHigh P.K₀
    hSM hM0 hL2' hLS' hHiStartup' hnextPos hnextParent hq0M hnShell with
      hterm | hfail
  · have hn8 : 8 ≤ n := by
      have hpow : 2 ^ 3 ≤ 2 ^ M := Nat.pow_le_pow_right (by omega) hM3
      exact hpow.trans (mem_dyadicShell.mp hnShell).1
    have hlog8 : 1 ≤ Real.log (8 : ℝ) := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      have hlog2Half : (1 / 2 : ℝ) < Real.log 2 :=
        (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
      norm_num only [Nat.cast_ofNat]
      nlinarith
    have hn8Real : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
    have hlogn : 1 ≤ Real.log n :=
      hlog8.trans (Real.log_le_log (by norm_num) hn8Real)
    have htarget := shellPolylogTarget_le_natLog hA0.le hnShell hlogn
    have hconst := timeout_fixedPolylogTargetConstant_mono hUpper
    have hlogPow0 : 0 ≤ (Real.log n) ^ (A M) :=
      Real.rpow_nonneg (zero_le_one.trans hlogn) _
    rcases hterm with hrunTerm | hdyadic
    · rcases hrunTerm with ⟨elapsed, q, hqL, hrun⟩
      have hlandingNat : orbit elapsed n ≤ 2 ^ L :=
        hrun.directFirstPassage.1.trans
          (Nat.pow_le_pow_right (by omega) hqL)
      have hlandingReal : (orbit elapsed n : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by
        exact_mod_cast hlandingNat
      have hterminal : ((2 ^ L : ℕ) : ℝ) <
          2 * (((M : ℝ) + 2) ^ (A M)) := by
        simpa [L] using two_pow_movingTerminalRank_lt hA0.le
      have hclockRun := hClock hrun
      have hclock : (elapsed : ℝ) < c * (M : ℝ) * Real.log 2 := by
        have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
        push_cast at hclockRun
        linarith
      have hcentered := hCentered (q := q) (L := L) (n := n)
        (elapsed := elapsed) (hqL.trans hLS') hrun
      have hqSub : q - L = 0 := Nat.sub_eq_zero_of_le hqL
      simp only [hqSub, add_zero] at hcentered
      have hrawBase := hRawCentered (q := q) (n := n)
        (elapsed := elapsed) (hqL.trans hLS') hrun
      have hrawCentered :
          |(2 * driftGap / 3) * (rawTime n elapsed : ℝ) - (M : ℝ)| ≤
            timeoutCompletedRawClockSupportConstant
                P.run.toTimeoutHigh P.Cswitch *
              Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
        let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
        have hroot0 : 0 ≤ root := Real.sqrt_nonneg _
        have hT0 : 0 ≤ timeoutTimeSupportConstant
            P.run.toTimeoutHigh P.Cswitch :=
          (timeoutTimeSupportConstant_pos P.run.toTimeoutHigh P.Cswitch).le
        change |(2 * driftGap / 3) * (rawTime n elapsed : ℝ) - (M : ℝ)| ≤
          (timeoutRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch +
            timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch) * root
        calc
          |(2 * driftGap / 3) * (rawTime n elapsed : ℝ) - (M : ℝ)| ≤
              timeoutRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch *
                root := by simpa [root] using hrawBase
          _ ≤ (timeoutRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch +
                timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch) *
              root := by nlinarith [mul_nonneg hT0 hroot0]
      have hheight := hrun.shortcut_raw_le_relative_height hR
        P.high_height_contraction.le hLowMargin hnShell hnMax
      let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
      have hroot0 : 0 ≤ root := Real.sqrt_nonneg _
      have hshortcutTube : ∀ j : ℕ, j ≤ elapsed →
          |shortcutLogDeviation n j| ≤
            2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch *
              root := by
        intro j hj
        have h := hShortcutTube hrun j hj
        have h' : |shortcutLogDeviation n j| ≤
            timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch * root := by
          simpa [root] using h
        have hnonneg : 0 ≤
            timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch * root :=
          mul_nonneg
            (timeoutTimeSupportConstant_pos
              P.run.toTimeoutHigh P.Cswitch).le hroot0
        nlinarith
      have hoddTube : ∀ j : ℕ, j ≤ elapsed →
          |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
            timeoutCompletedOddTrajectorySupportConstant
                P.run.toTimeoutHigh P.Cswitch * root := by
        intro j hj
        have h := hOddTube hrun j hj
        exact h.trans (mul_le_mul_of_nonneg_right
          (timeoutOddTrajectorySupportConstant_le_completed _ _) hroot0)
      have hrawTube : ∀ i : ℕ, i ≤ rawTime n elapsed →
          |rawLogDeviation n i| ≤
            timeoutCompletedRawTrajectorySupportConstant
                P.run.toTimeoutHigh P.Cswitch * root := by
        intro i hi
        have h := hRawTube hrun i hi
        exact h.trans (mul_le_mul_of_nonneg_right
          (timeoutRawTrajectorySupportConstant_le_completed _ _) hroot0)
      refine ⟨elapsed, rawTime n elapsed, hclock, hcentered, hrawCentered,
        hshortcutTube, hoddTube, hrawTube, rfl,
        rawOrbit_rawTime_eq_orbit n elapsed,
        hlandingReal.trans_lt (hterminal.trans_le (htarget.trans
          (mul_le_mul_of_nonneg_right hconst hlogPow0))), hheight.1, ?_⟩
      simpa using hheight.2
    · rcases hdyadic with ⟨elapsed, q, hLq, hqS, hrun, heq⟩
      let v := q - L
      let k := elapsed + v
      have hvq : v ≤ q := Nat.sub_le _ _
      have horbitV : orbit v (2 ^ q) = 2 ^ L := by
        rw [timeout_orbit_two_pow hvq]
        congr
        omega
      have hlandingNat : orbit k n = 2 ^ L := by
        dsimp [k]
        rw [add_comm, orbit_add, heq, horbitV]
      have hlandingReal : (orbit k n : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by
        exact_mod_cast hlandingNat.le
      have hterminal : ((2 ^ L : ℕ) : ℝ) <
          2 * (((M : ℝ) + 2) ^ (A M)) := by
        simpa [L] using two_pow_movingTerminalRank_lt hA0.le
      have hclockRun := hClock hrun
      have hvS : v ≤ S := (Nat.sub_le q L).trans hqS
      have hkBound : k ≤ elapsed + S := Nat.add_le_add_left hvS elapsed
      have hclock : (k : ℝ) < c * (M : ℝ) * Real.log 2 := by
        have hkR : (k : ℝ) ≤ ((elapsed + S : ℕ) : ℝ) := by
          exact_mod_cast hkBound
        exact hkR.trans_lt hclockRun
      have hcentered :
          |driftGap * (k : ℝ) - (M : ℝ)| ≤
            2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch *
              Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
        simpa [k, v] using hCentered (q := q) (L := L) (n := n)
          (elapsed := elapsed) hqS hrun
      have hrawCentered :
          |(2 * driftGap / 3) * (rawTime n k : ℝ) - (M : ℝ)| ≤
            timeoutCompletedRawClockSupportConstant
                P.run.toTimeoutHigh P.Cswitch *
              Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
        simpa [k, v] using hRawCompleted (L := L) (n := n)
          (elapsed := elapsed) (q := q) rfl hqS hrun heq
      have hrunHeight := hrun.shortcut_raw_le_relative_height hR
        P.high_height_contraction.le hLowMargin hnShell hnMax
      have hlater : (n : ℝ) ≤ (n : ℝ) * R M / 2 := by
        have hn0 : (0 : ℝ) ≤ n := by positivity
        nlinarith
      have hshortcut : ∀ j : ℕ, j ≤ k →
          (orbit j n : ℝ) ≤ (n : ℝ) * R M / 2 := by
        intro j hj
        by_cases hjElapsed : j ≤ elapsed
        · exact hrunHeight.1 j hjElapsed
        · let u := j - elapsed
          have hjForm : j = u + elapsed := by dsimp [u]; omega
          have huV : u ≤ v := by dsimp [u, k] at hj ⊢; omega
          have huq : u ≤ q := huV.trans hvq
          have huOrbit : orbit u (2 ^ q) = 2 ^ (q - u) :=
            timeout_orbit_two_pow huq
          have htailNat : orbit j n ≤ orbit elapsed n := by
            rw [hjForm, orbit_add, heq, huOrbit]
            exact Nat.pow_le_pow_right (by omega) (Nat.sub_le q u)
          have htail : (orbit j n : ℝ) ≤ (n : ℝ) := by
            have hEndpoint : orbit elapsed n ≤ n :=
              (hrun.endpoint_lt_start hnShell).le
            exact_mod_cast htailNat.trans hEndpoint
          exact htail.trans hlater
      have hraw : ∀ i : ℕ, i ≤ rawTime n k →
          (rawOrbit i n : ℝ) ≤ (n : ℝ) * R M := by
        intro i hi
        have hi' := rawOrbit_le_two_mul_of_shortcut_prefix_le hshortcut i hi
        convert hi' using 1 <;> ring
      have hshortcutTube := hShortcutCompleted hrun hvS
      have hoddTube := hOddCompleted hrun heq hvq hvS
      have hrawTube := hRawTrajectoryCompleted hrun heq hvq hvS
      refine ⟨k, rawTime n k, hclock, hcentered, hrawCentered,
        (by simpa [k, v] using hshortcutTube),
        (by simpa [k, v] using hoddTube),
        (by simpa [k, v] using hrawTube), rfl,
        rawOrbit_rawTime_eq_orbit n k,
        hlandingReal.trans_lt (hterminal.trans_le (htarget.trans
          (mul_le_mul_of_nonneg_right hconst hlogPow0))),
        hshortcut, ?_⟩
      simpa using hraw
  · exact False.elim (hnNotFailure hfail)
end FirstPassageLinearTransport

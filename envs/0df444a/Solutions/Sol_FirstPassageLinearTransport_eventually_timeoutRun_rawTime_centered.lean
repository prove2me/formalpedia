-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_timeoutRun_rawTime_centered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:20:23.554441+00:00
-- url     : https://prove2.me/submissions/645e2cb0-6e7b-451e-a74a-57ae07fa4d49

import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Theorems.Thm_FirstPassageLinearTransport_oddCount_centered_of_firstPassage_reverseProduct_half
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_reverseProduct_half
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_elapsed_pos
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_deviation_add_potential_le
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_elapsed_pos
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_deviation_add_potential_le
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_elapsed_pos
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_source_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_elapsed_centered
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutTimePotential_source_le_sqrt
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
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimePotential_nonneg
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
      q ≤ shrinkingSwitchRank P.Cswitch M →
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
        (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
        n elapsed q →
      |(2 * driftGap / 3) * (rawTime n elapsed : ℝ) - (M : ℝ)| ≤
        timeoutRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  let T := timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch
  have hReverse := eventually_timeoutRun_reverseProduct_half P hbuffer
  have hElapsed := eventually_timeoutRun_elapsed_centered
    (K₀ := P.K₀) P.run.toTimeoutHigh P.Cswitch_pos.le
  have hPotential := eventually_timeoutTimePotential_source_le_sqrt
    P.run.toTimeoutHigh P.Cswitch_pos.le
  filter_upwards [hReverse, hElapsed, hPotential,
      eventually_ge_atTop (1 : ℕ)]
    with M hReverse hElapsed hPotential hM
  intro n elapsed q hqS hrun
  let S := shrinkingSwitchRank P.Cswitch M
  let sourcePotential := timeoutTimePotential P.run.toTimeoutHigh M S (M + 1)
  let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  have hnShell := hrun.source_mem_dyadicShell
  have hn : 0 < n := by
    have hlo := (mem_dyadicShell.mp hnShell).1
    have hpow : 0 < 2 ^ M := by positivity
    omega
  have hP := hReverse hrun
  have hdev := hrun.deviation_add_potential_le hM
  have hpotq0 := timeoutTimePotential_nonneg P.run.toTimeoutHigh M S q
  have hlocal :
      |driftGap * (elapsed : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤ sourcePotential := by
    dsimp [sourcePotential, S]
    linarith
  have hodd := oddCount_centered_of_firstPassage_reverseProduct_half
    hn hnShell hrun.elapsed_pos hrun.directFirstPassage hP hlocal
  have hElapsed' := hElapsed hqS hrun
  have hpot0 : 0 ≤ sourcePotential := by
    dsimp [sourcePotential, S]
    exact timeoutTimePotential_nonneg P.run.toTimeoutHigh M
      (shrinkingSwitchRank P.Cswitch M) (M + 1)
  have hlog1 : 1 ≤ Real.log ((M : ℝ) + 2) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hroot1 : 1 ≤ root := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hdivBound : 2 * sourcePotential / driftGap ≤ T * root := by
    dsimp [T, root, sourcePotential, S] at hPotential ⊢
    linarith
  have hpotBound :
      sourcePotential ≤ driftGap / 2 * T * root := by
    rw [div_le_iff₀ driftGap_pos] at hdivBound
    nlinarith
  have hTpos : 0 < T := by
    by_contra hT
    have hTnonpos : T ≤ 0 := le_of_not_gt hT
    have hroot0 : 0 ≤ root := Real.sqrt_nonneg _
    have hright : T * root ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hTnonpos hroot0
    have hleft : 0 ≤ 2 * sourcePotential / driftGap :=
      div_nonneg (mul_nonneg (by norm_num) hpot0) driftGap_pos.le
    linarith
  have hoddScale :
      |(oddCount n elapsed : ℝ) - (elapsed : ℝ) / 2| ≤
        (driftGap / 2 * T + 2) * root * Real.log 2 / Real.log 3 := by
    have hbase : sourcePotential + 2 ≤
        (driftGap / 2 * T + 2) * root := by
      have htwo : (2 : ℝ) ≤ 2 * root := by linarith
      have hcoef0 : 0 ≤ driftGap / 2 * T :=
        mul_nonneg (div_nonneg driftGap_pos.le (by norm_num)) hTpos.le
      calc
        sourcePotential + 2 ≤ driftGap / 2 * T * root + 2 * root :=
          add_le_add hpotBound htwo
        _ = (driftGap / 2 * T + 2) * root := by ring
    exact hodd.trans (by
      apply (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num))).2
      exact mul_le_mul_of_nonneg_right hbase
        (Real.log_nonneg (by norm_num)))
  have hrawCast : (rawTime n elapsed : ℝ) =
      (elapsed : ℝ) + (oddCount n elapsed : ℝ) := by
    simp [rawTime]
  have hcoef0 : 0 ≤ 2 * driftGap / 3 :=
    div_nonneg (mul_nonneg (by norm_num) driftGap_pos.le) (by norm_num)
  calc
    |(2 * driftGap / 3) * (rawTime n elapsed : ℝ) - (M : ℝ)| =
        |(driftGap * (elapsed : ℝ) - (M : ℝ)) +
          (2 * driftGap / 3) *
            ((oddCount n elapsed : ℝ) - (elapsed : ℝ) / 2)| := by
      rw [hrawCast]
      ring_nf
    _ ≤ |driftGap * (elapsed : ℝ) - (M : ℝ)| +
          |(2 * driftGap / 3) *
            ((oddCount n elapsed : ℝ) - (elapsed : ℝ) / 2)| := abs_add_le _ _
    _ = |driftGap * (elapsed : ℝ) - (M : ℝ)| +
          (2 * driftGap / 3) *
            |(oddCount n elapsed : ℝ) - (elapsed : ℝ) / 2| := by
      rw [abs_mul, abs_of_nonneg hcoef0]
    _ ≤ T * root + (2 * driftGap / 3) *
          ((driftGap / 2 * T + 2) * root * Real.log 2 / Real.log 3) :=
      add_le_add hElapsed' (mul_le_mul_of_nonneg_left hoddScale hcoef0)
    _ = timeoutRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch * root := by
      dsimp [timeoutRawClockSupportConstant, T]
      ring
end FirstPassageLinearTransport

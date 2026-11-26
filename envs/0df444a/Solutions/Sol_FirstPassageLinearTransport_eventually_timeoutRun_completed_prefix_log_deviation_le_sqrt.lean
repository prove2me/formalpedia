-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_timeoutRun_completed_prefix_log_deviation_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:23.722145+00:00
-- url     : https://prove2.me/submissions/563ed5e1-b761-40f9-9bde-3a89a54d4582

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_shortcutLogDeviation_add
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_abs_shortcutLogDeviation_le_two_mul
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_prefix_log_deviation_le_sqrt
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_source_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_a0_pos
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_eventually_shrinkingSwitchRank_lt_source
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
import Theorems.Thm_FirstPassageLinearTransport_orbit_pos
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimePotential_nonneg
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimeSupportConstant_pos
import Theorems.Thm_FirstPassageLinearTransport_timeout_switch_sq_le_source_potential
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
    (P : TimeoutHighRunData) {K₀ C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop, ∀ {L n elapsed q v : ℕ},
      TimeoutRecertificationRun P K₀ L M
        (shrinkingSwitchRank C M) n elapsed q →
      v ≤ shrinkingSwitchRank C M →
      ∀ j : ℕ, j ≤ elapsed + v →
        |shortcutLogDeviation n j| ≤
          2 * timeoutTimeSupportConstant P C *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  filter_upwards [eventually_timeoutRun_prefix_log_deviation_le_sqrt P hC,
      eventually_timeoutTimePotential_source_le_sqrt P hC,
      eventually_shrinkingSwitchRank_lt_source hC,
      eventually_ge_atTop (1 : ℕ)]
    with M htube hsupport hswitch hM
  intro L n elapsed q v hrun hv j hj
  let S := shrinkingSwitchRank C M
  let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  have hroot0 : 0 ≤ root := Real.sqrt_nonneg _
  have htime0 : 0 < timeoutTimeSupportConstant P C :=
    timeoutTimeSupportConstant_pos P C
  have hsourcePot0 := timeoutTimePotential_nonneg P M S (M + 1)
  have hgap1 : driftGap ≤ 1 := by
    unfold driftGap
    linarith [a0_pos]
  have hdiv : 2 * timeoutTimePotential P M S (M + 1) ≤
      2 * timeoutTimePotential P M S (M + 1) / driftGap := by
    rw [le_div_iff₀ driftGap_pos]
    nlinarith [mul_nonneg hsourcePot0 driftGap_pos.le]
  have hpotBound : 2 * timeoutTimePotential P M S (M + 1) ≤
      timeoutTimeSupportConstant P C * root := by
    calc
      _ ≤ 2 * timeoutTimePotential P M S (M + 1) / driftGap := hdiv
      _ ≤ 1 + 2 * timeoutTimePotential P M S (M + 1) / driftGap := by
        linarith
      _ ≤ _ := by simpa [S, root] using hsupport
  have hswitchSq : (S : ℝ) ^ 2 ≤
      timeoutTimePotential P M S (M + 1) := by
    apply timeout_switch_sq_le_source_potential
    dsimp [S]
    exact hswitch.trans (Nat.lt_succ_self M)
  have hSbound : 2 * (S : ℝ) ≤
      timeoutTimeSupportConstant P C * root := by
    have htwoS : 2 * (S : ℝ) ≤ 1 + (S : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((S : ℝ) - 1)]
    have honePot : 1 + (S : ℝ) ^ 2 ≤
        1 + 2 * timeoutTimePotential P M S (M + 1) / driftGap := by
      have hpotDiv : timeoutTimePotential P M S (M + 1) ≤
          2 * timeoutTimePotential P M S (M + 1) / driftGap := by
        rw [le_div_iff₀ driftGap_pos]
        nlinarith [mul_nonneg hsourcePot0 driftGap_pos.le]
      linarith
    exact htwoS.trans (honePot.trans (by simpa [S, root] using hsupport))
  by_cases hjOld : j ≤ elapsed
  · have h := htube hrun j hjOld
    nlinarith [mul_nonneg htime0.le hroot0]
  · let u := j - elapsed
    have hjForm : j = u + elapsed := by
      dsimp [u]
      omega
    have huV : u ≤ v := by
      dsimp [u]
      omega
    have huS : (u : ℝ) ≤ S := by
      exact_mod_cast huV.trans hv
    have hn : 0 < n := by
      have hnShell := hrun.source_mem_dyadicShell
      have hnLower := (mem_dyadicShell.mp hnShell).1
      have hpow : 0 < 2 ^ M := by positivity
      omega
    have hlocal := abs_shortcutLogDeviation_le_two_mul
      (n := orbit elapsed n) (j := u) (orbit_pos hn elapsed)
    have hbase := htube hrun elapsed le_rfl
    have hadd := shortcutLogDeviation_add n elapsed u
    have habs := abs_add_le (shortcutLogDeviation n elapsed)
      (shortcutLogDeviation (orbit elapsed n) u)
    rw [← hadd, ← hjForm] at habs
    nlinarith
end FirstPassageLinearTransport

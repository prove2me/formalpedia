-- Prove2me | solution 1 for FirstPassageLinearTransport.TimeoutRecertificationRun.prefix_log_deviation_add_potential_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:06.225136+00:00
-- url     : https://prove2.me/submissions/713034ef-0ff9-4356-bf6c-0c15b6f21117

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_shortcutLogDeviation_add
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_abs_shortcutLogDeviation_le_two_mul
import Theorems.Thm_FirstPassageLinearTransport_abs_shortcutLogDeviation_highStage_le_durationError
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_M0_pos
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
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
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimePotential_high_step
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
namespace TimeoutRecertificationRun
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed q : ℕ} (hM : 1 ≤ M)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    ∀ j : ℕ, j ≤ elapsed →
      |shortcutLogDeviation n j| + 2 * timeoutTimePotential P M S q ≤
        2 * timeoutTimePotential P M S (M + 1) := by
  induction hrun with
  | first hSM hM0 hnShell hnGood =>
      intro j hj
      have hlocal := abs_shortcutLogDeviation_highStage_le_durationError
        P hM0 hnShell hnGood hj
      have hq : (rationalTargetRank P.rHi M : ℝ) ≤
          (P.rHi : ℝ) * (M : ℝ) := by
        have hnonneg : 0 ≤ (P.rHi : ℝ) * (M : ℝ) :=
          mul_nonneg P.pHi.r_pos.le (Nat.cast_nonneg M)
        exact Nat.floor_le hnonneg
      have hstep := timeoutTimePotential_high_step P
        (S := S) (m := M) (q := rationalTargetRank P.rHi M)
        hM hM hSM hq
      have hcost0 : 0 ≤
          timeoutDurationError (timeoutHighTolerance P M M) M := by
        have ht0 := (timeoutHighTolerance_pos P M M).le
        have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
        unfold timeoutDurationError
        nlinarith [mul_nonneg ht0 hM0]
      nlinarith
  | @nextHi elapsed qPrev m hrun hSm hm0 hmPrev hsourceShell hsourceGood
      hgap ih =>
      intro j hj
      have hq : (rationalTargetRank P.rHi m : ℝ) ≤
          (P.rHi : ℝ) * (m : ℝ) := by
        have hnonneg : 0 ≤ (P.rHi : ℝ) * (m : ℝ) :=
          mul_nonneg P.pHi.r_pos.le (Nat.cast_nonneg m)
        exact Nat.floor_le hnonneg
      have hm1 : 1 ≤ m := P.pHi.M0_pos.trans hm0
      have hstep0 := timeoutTimePotential_high_step P
        (M := M) (S := S) (m := m) (q := rationalTargetRank P.rHi m)
        hM hm1 hSm hq
      have hstep :
          timeoutDurationError (timeoutHighTolerance P M m) m +
              timeoutTimePotential P M S (rationalTargetRank P.rHi m) ≤
            timeoutTimePotential P M S qPrev := by
        simpa [hmPrev] using hstep0
      have hcost0 : 0 ≤
          timeoutDurationError (timeoutHighTolerance P M m) m := by
        have ht0 := (timeoutHighTolerance_pos P M m).le
        have hm0R : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        unfold timeoutDurationError
        nlinarith [mul_nonneg ht0 hm0R]
      by_cases hjOld : j ≤ elapsed
      · have hIH := ih j hjOld
        nlinarith
      · let u := j - elapsed
        have hjForm : j = u + elapsed := by
          dsimp [u]
          omega
        have huStage : u ≤
            stageLength (timeoutHighSetup P M m) (orbit elapsed n) := by
          dsimp [u]
          omega
        have hlocal := abs_shortcutLogDeviation_highStage_le_durationError
          P hm0 hsourceShell hsourceGood huStage
        have hIH := ih elapsed le_rfl
        have hadd := shortcutLogDeviation_add n elapsed u
        have habs := abs_add_le (shortcutLogDeviation n elapsed)
          (shortcutLogDeviation (orbit elapsed n) u)
        rw [← hadd, ← hjForm] at habs
        nlinarith

  | @nextLo elapsed qPrev m hrun hmS hLm hmPrevLo hmPrevHi hsourceShell
      hpass hqpos hqparent hgap ih =>
      intro j hj
      let qNext := timeoutTargetRank K₀ L m
      have hqLow : ¬S < qNext := by
        dsimp [qNext]
        omega
      have hprevLow : ¬S < qPrev := by omega
      have hmR : (m : ℝ) ≤ qPrev := by exact_mod_cast hmPrevLo
      have hqR : (qNext : ℝ) + 1 ≤ m := by
        dsimp [qNext]
        exact_mod_cast hqparent
      have hSR : (m : ℝ) + 1 ≤ S := by exact_mod_cast hmS
      have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
      have hpay : (m : ℝ) + timeoutTimePotential P M S qNext ≤
          timeoutTimePotential P M S qPrev := by
        simp only [timeoutTimePotential, if_neg hqLow, if_neg hprevLow]
        nlinarith [mul_nonneg hS0 (sub_nonneg.mpr hqR)]
      by_cases hjOld : j ≤ elapsed
      · have hIH := ih j hjOld
        have hm0Real : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith
      · let u := j - elapsed
        have hjForm : j = u + elapsed := by
          dsimp [u]
          omega
        have huDuration : u ≤ hpass.duration := by
          dsimp [u]
          omega
        have hsourcePos : 0 < orbit elapsed n := by
          have hsourceLower := (mem_dyadicShell.mp hsourceShell).1
          have hpow : 0 < 2 ^ m := by positivity
          omega
        have hlocal := abs_shortcutLogDeviation_le_two_mul
          (n := orbit elapsed n) (j := u) hsourcePos
        have huM : (u : ℝ) ≤ m := by
          exact_mod_cast huDuration.trans hpass.duration_le
        have hIH := ih elapsed le_rfl
        have hadd := shortcutLogDeviation_add n elapsed u
        have habs := abs_add_le (shortcutLogDeviation n elapsed)
          (shortcutLogDeviation (orbit elapsed n) u)
        rw [← hadd, ← hjForm] at habs
        nlinarith
end TimeoutRecertificationRun
end FirstPassageLinearTransport

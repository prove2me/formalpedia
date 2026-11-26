-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutDurationError_high_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:28.84993+00:00
-- url     : https://prove2.me/submissions/8cadb450-e6e8-4efa-8e59-2acb05e61c0f

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
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
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
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
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
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
    (P : TimeoutHighRunData) {M m : ℕ}
    (hM : 1 ≤ M) (hm : 1 ≤ m) :
    timeoutDurationError (timeoutHighTolerance P M m) m ≤
      (P.D + P.tau + 3) *
        Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog1 : 1 ≤ Real.log ((M : ℝ) + 2) := by
    have hM3 : Real.exp 1 ≤ (M : ℝ) + 2 := by
      have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    simpa using (Real.le_log_iff_exp_le (by positivity)).2 hM3
  have hsqrtLog1 : 1 ≤ Real.sqrt (Real.log ((M : ℝ) + 2)) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hlog1
  have hsqrtM1 : 1 ≤ Real.sqrt (m : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hm)
  have htD : timeoutHighTolerance P M m ≤
      P.D * Real.sqrt (Real.log ((M : ℝ) + 2) / (m : ℝ)) := by
    simp [timeoutHighTolerance, Nat.ne_of_gt hm]
  have hsqrtm0 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm0
  have hmain :
      Real.sqrt (Real.log ((M : ℝ) + 2) / (m : ℝ)) * (m : ℝ) =
        Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt (m : ℝ) := by
    have harg : (1 : ℝ) ≤ (M : ℝ) + 2 := by
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      linarith
    rw [Real.sqrt_div (Real.log_nonneg harg)]
    field_simp [hsqrtm0.ne']
    nlinarith [Real.sq_sqrt hm0.le]
  have htmain : timeoutHighTolerance P M m * (m : ℝ) ≤
      P.D * Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt m := by
    calc
      timeoutHighTolerance P M m * (m : ℝ) ≤
          (P.D * Real.sqrt
            (Real.log ((M : ℝ) + 2) / (m : ℝ))) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right htD hm0.le
      _ = P.D * Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt m := by
        rw [mul_assoc, hmain]
        ring
  have htcap := timeoutHighTolerance_le_tau P M m
  have hscale1 : 1 ≤
      Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt (m : ℝ) :=
    one_le_mul_of_one_le_of_one_le hsqrtLog1 hsqrtM1
  unfold timeoutDurationError
  calc
    timeoutHighTolerance P M m * (m : ℝ) +
          timeoutHighTolerance P M m + 3 ≤
        P.D * Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt m +
          P.tau + 3 := by linarith
    _ ≤ (P.D + P.tau + 3) *
          Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt m := by
      have hD0 := P.D_pos.le
      have htau0 := P.pHi.eta_pos.le
      nlinarith [mul_nonneg (add_nonneg htau0 (by norm_num : (0 : ℝ) ≤ 3))
        (sub_nonneg.mpr hscale1)]
end FirstPassageLinearTransport

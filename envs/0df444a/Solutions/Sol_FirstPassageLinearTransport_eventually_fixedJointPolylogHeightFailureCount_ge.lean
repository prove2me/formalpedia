-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_fixedJointPolylogHeightFailureCount_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:24.3515+00:00
-- url     : https://prove2.me/submissions/070a852c-4d78-4b63-bf05-bb19ce2ed003

import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
import Theorems.Thm_FirstPassageLinearTransport_eventually_fixedJointPolylogTarget_lt_halfShell
import Theorems.Thm_FirstPassageLinearTransport_fixedJointPolylogHeight_eq_on_shell
import Theorems.Thm_FirstPassageLinearTransport_eventually_log_shellRankRpow_le_halfShell
import Theorems.Thm_FirstPassageLinearTransport_eventually_half_le_reciprocalMaximum_halfShell_correction
import Theorems.Thm_FirstPassageLinearTransport_tendsto_lastCompleteDyadicShell_atTop
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
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_variableTargetHeightFailureCount_ge_reciprocal_lastCompleteShell
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



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {C A q : ℝ} (hC : 0 < C) (hA : 0 ≤ A) (hq : 0 < q) :
    ∀ᶠ X : ℕ in atTop,
      (X : ℝ) /
          (12 * (((lastCompleteDyadicShell X : ℕ) : ℝ) + 2) ^ q) ≤
        variableTargetHeightFailureCount
          (fixedJointPolylogTarget C A) (fixedJointPolylogHeight q) X := by
  have hTargetM := eventually_fixedJointPolylogTarget_lt_halfShell hC hA
  have hLogM := eventually_log_shellRankRpow_le_halfShell hq.le
  have hCorrectionM :=
    eventually_half_le_reciprocalMaximum_halfShell_correction
  have hMlarge : ∀ᶠ M : ℕ in atTop, 2 ≤ M := eventually_ge_atTop 2
  have hTarget := tendsto_lastCompleteDyadicShell_atTop.eventually hTargetM
  have hLog := tendsto_lastCompleteDyadicShell_atTop.eventually hLogM
  have hCorrection :=
    tendsto_lastCompleteDyadicShell_atTop.eventually hCorrectionM
  have hLarge := tendsto_lastCompleteDyadicShell_atTop.eventually hMlarge
  filter_upwards [eventually_ge_atTop (4 : ℕ), hTarget, hLog,
    hCorrection, hLarge] with X hX hTarget hLog hCorrection hMlarge
  let M := lastCompleteDyadicShell X
  let h := M / 2
  let U := ((M : ℝ) + 2) ^ q
  have hh : 0 < h := by dsimp [h]; omega
  have hhM : h ≤ M := by dsimp [h]; omega
  have hbase : 1 ≤ (M : ℝ) + 2 := by
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hU : 1 ≤ U := by
    dsimp [U]
    exact Real.one_le_rpow hbase hq.le
  have hUPos : 0 < U := zero_lt_one.trans_le hU
  have hLog' : Real.log U ≤
      reciprocalMaximumEpsilon * (h : ℝ) * Real.log 3 := by
    simpa [M, h, U] using hLog
  have hTarget' : ∀ n : ℕ, n ∈ dyadicShell M →
      fixedJointPolylogTarget C A n <
        (n : ℝ) / (2 : ℝ) ^ h := by
    simpa [M, h] using hTarget
  have hHeight : ∀ n : ℕ, n ∈ dyadicShell M →
      fixedJointPolylogHeight q n ≤ U := by
    intro n hn
    rw [fixedJointPolylogHeight_eq_on_shell q hn]
  have hraw :=
    variableTargetHeightFailureCount_ge_reciprocal_lastCompleteShell
      hX hU hLog' hh hhM hTarget' hHeight
  have hcoef0 : 0 ≤ (1 / 4 : ℝ) * (2 / (3 * U)) := by positivity
  have hX0 : 0 ≤ (X : ℝ) := by positivity
  have hweaken :
      ((1 / 4 : ℝ) * (2 / (3 * U)) * (1 / 2)) * (X : ℝ) ≤
        ((1 / 4 : ℝ) * (2 / (3 * U)) *
          (1 - reciprocalMaximumConstant / (h : ℝ))) * (X : ℝ) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hCorrection hcoef0) hX0
  have hsimple :
      (X : ℝ) / (12 * U) =
        ((1 / 4 : ℝ) * (2 / (3 * U)) * (1 / 2)) * (X : ℝ) := by
    field_simp [ne_of_gt hUPos]
    ring
  rw [hsimple]
  exact hweaken.trans (by simpa [M, h, U] using hraw)
end FirstPassageLinearTransport

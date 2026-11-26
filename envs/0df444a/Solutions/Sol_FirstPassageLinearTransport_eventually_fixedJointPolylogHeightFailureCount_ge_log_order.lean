-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_fixedJointPolylogHeightFailureCount_ge_log_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:54.341854+00:00
-- url     : https://prove2.me/submissions/dd5501b0-bdb2-40d8-88fb-2f0ed706f389

import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
import Theorems.Thm_FirstPassageLinearTransport_eventually_fixedJointPolylogHeightFailureCount_ge
import Theorems.Thm_FirstPassageLinearTransport_lastCompleteDyadicShell_add_two
import Theorems.Thm_FirstPassageLinearTransport_natLogTwo_add_one_le_two_div_log_two_mul_log
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
      (1 / (12 * (2 / Real.log 2) ^ q)) * (X : ℝ) *
          (Real.log X) ^ (-q) ≤
        variableTargetHeightFailureCount
          (fixedJointPolylogTarget C A) (fixedJointPolylogHeight q) X := by
  have hraw := eventually_fixedJointPolylogHeightFailureCount_ge hC hA hq
  filter_upwards [hraw, eventually_ge_atTop (4 : ℕ)] with X hraw hX
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKPos : 0 < 2 / Real.log 2 := by positivity
  have hlogXPos : 0 < Real.log X :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hbase :
      (((lastCompleteDyadicShell X : ℕ) : ℝ) + 2) ≤
        (2 / Real.log 2) * Real.log X := by
    rw [show ((lastCompleteDyadicShell X : ℕ) : ℝ) + 2 =
      (((Nat.log 2 X : ℕ) : ℝ) + 1) by
        exact_mod_cast lastCompleteDyadicShell_add_two hX]
    exact natLogTwo_add_one_le_two_div_log_two_mul_log (by omega)
  have hbase0 : 0 ≤ ((lastCompleteDyadicShell X : ℕ) : ℝ) + 2 := by
    positivity
  have hpow :
      (((lastCompleteDyadicShell X : ℕ) : ℝ) + 2) ^ q ≤
        ((2 / Real.log 2) * Real.log X) ^ q :=
    Real.rpow_le_rpow hbase0 hbase hq.le
  have hfactor :
      (((lastCompleteDyadicShell X : ℕ) : ℝ) + 2) ^ q ≤
        (2 / Real.log 2) ^ q * (Real.log X) ^ q := by
    simpa [Real.mul_rpow hKPos.le hlogXPos.le] using hpow
  have hdenPos : 0 <
      12 * (((lastCompleteDyadicShell X : ℕ) : ℝ) + 2) ^ q := by
    positivity
  have hdiv :
      (X : ℝ) /
          (12 * ((2 / Real.log 2) ^ q * (Real.log X) ^ q)) ≤
        (X : ℝ) /
          (12 * (((lastCompleteDyadicShell X : ℕ) : ℝ) + 2) ^ q) := by
    exact div_le_div_of_nonneg_left (by positivity) hdenPos
      (mul_le_mul_of_nonneg_left hfactor (by norm_num))
  have hrewrite :
      (1 / (12 * (2 / Real.log 2) ^ q)) * (X : ℝ) *
          (Real.log X) ^ (-q) =
        (X : ℝ) /
          (12 * ((2 / Real.log 2) ^ q * (Real.log X) ^ q)) := by
    rw [Real.rpow_neg hlogXPos.le]
    field_simp
  rw [hrewrite]
  exact hdiv.trans hraw
end FirstPassageLinearTransport

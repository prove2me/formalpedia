-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_criticalMultiplierExponent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:55.661727+00:00
-- url     : https://prove2.me/submissions/43a13ab3-890e-4741-8550-3089dd8a7b20

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Theorems.Thm_FirstPassageLinearTransport_tendsto_clippedCriticalMultiplier_atTop
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
import Theorems.Thm_FirstPassageLinearTransport_timeSupportCriticalExponent_pos
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
    {U : ℕ → ℝ} (hU : Tendsto U atTop atTop) :
    ∀ᶠ M : ℕ in atTop,
      criticalMultiplierExponent U M < timeSupportCriticalExponent + 2 := by
  have hwT := tendsto_clippedCriticalMultiplier_atTop hU
  have hw1 : ∀ᶠ M : ℕ in atTop, 1 ≤ clippedCriticalMultiplier U M :=
    (tendsto_atTop.1 hwT) 1
  filter_upwards [hw1] with M hw1
  let x : ℝ := (M : ℝ) + 2
  let w : ℝ := clippedCriticalMultiplier U M
  have hx2 : 2 ≤ x := by
    dsimp [x]
    exact le_add_of_nonneg_left (Nat.cast_nonneg M)
  have hx : 0 < x := zero_lt_two.trans_le hx2
  have hw : 0 < w := zero_lt_one.trans_le hw1
  have hlogx : 0 < Real.logb 2 x :=
    Real.logb_pos (by norm_num) (by linarith)
  have hlogx1 : 1 ≤ Real.logb 2 x := by
    have := Real.logb_le_logb_of_le (b := (2 : ℝ))
      (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2) hx2
    simpa using this
  have hwle : w ≤ x := by
    dsimp [w, clippedCriticalMultiplier]
    exact min_le_right _ _
  have hlogw : Real.logb 2 w ≤ Real.logb 2 x :=
    Real.logb_le_logb_of_le (b := (2 : ℝ))
      (by norm_num : (1 : ℝ) < 2) hw hwle
  have htotal0 : 0 ≤
      timeSupportCriticalExponent * Real.logb 2 x + Real.logb 2 w := by
    have hlogw0 : 0 ≤ Real.logb 2 w :=
      Real.logb_nonneg (by norm_num) hw1
    exact add_nonneg
      (mul_nonneg timeSupportCriticalExponent_pos.le hlogx.le) hlogw0
  have hceil : (criticalMultiplierTerminalRank U M : ℝ) <
      timeSupportCriticalExponent * Real.logb 2 x + Real.logb 2 w + 1 := by
    simpa [criticalMultiplierTerminalRank, x, w] using
      (Nat.ceil_lt_add_one htotal0)
  have hrank : (criticalMultiplierTerminalRank U M : ℝ) <
      (timeSupportCriticalExponent + 2) * Real.logb 2 x := by
    calc
      (criticalMultiplierTerminalRank U M : ℝ) <
          timeSupportCriticalExponent * Real.logb 2 x +
            Real.logb 2 w + 1 := hceil
      _ ≤ (timeSupportCriticalExponent + 2) * Real.logb 2 x := by
        nlinarith
  rw [criticalMultiplierExponent]
  exact (div_lt_iff₀ hlogx).2 (by simpa [x] using hrank)
end FirstPassageLinearTransport

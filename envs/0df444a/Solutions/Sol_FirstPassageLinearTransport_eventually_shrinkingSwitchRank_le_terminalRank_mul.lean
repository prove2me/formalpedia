-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_shrinkingSwitchRank_le_terminalRank_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:12.090862+00:00
-- url     : https://prove2.me/submissions/d4f32ae1-a96b-4dbe-9b8d-bdd1f42cc562

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointRate_eq_entropyGap_mul_logTwo
import Theorems.Thm_FirstPassageLinearTransport_movingRankBuffer_eq
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingTerminalRank_atTop
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
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
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_shrinkingSwitchRank_lt_add_one
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
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
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop,
      (shrinkingSwitchRank C M : ℝ) ≤
        (2 * C * firstPassageEndpointRate + 1) *
          (movingTerminalRank A M : ℝ) := by
  have hbuf0 : ∀ᶠ M : ℕ in atTop, 0 ≤ movingRankBuffer A M :=
    (tendsto_atTop.1 hbuffer) 0
  have hRank := (tendsto_atTop.1
    (tendsto_movingTerminalRank_atTop hbuffer)) 1
  filter_upwards [hbuf0, hRank, eventually_ge_atTop (1 : ℕ)]
    with M hbuf0 hRank hM
  let L := movingTerminalRank A M
  have hlog1 : 1 ≤ Real.log ((M : ℝ) + 3) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hloglog0 : 0 ≤ Real.logb 2 (Real.log ((M : ℝ) + 3)) :=
    Real.logb_nonneg (by norm_num) hlog1
  have hlogbBound : Real.logb 2 ((M : ℝ) + 2) ≤
      2 * firstPassageEntropyGap * (L : ℝ) := by
    rw [movingRankBuffer_eq] at hbuf0
    dsimp [L]
    linarith
  have hlogIdentity : Real.log ((M : ℝ) + 2) =
      Real.log 2 * Real.logb 2 ((M : ℝ) + 2) := by
    simp [Real.logb]
    field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hlogBound : Real.log ((M : ℝ) + 2) ≤
      2 * firstPassageEndpointRate * (L : ℝ) := by
    rw [hlogIdentity, firstPassageEndpointRate_eq_entropyGap_mul_logTwo]
    have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    nlinarith [mul_le_mul_of_nonneg_left hlogbBound hlog2]
  have hswitch := shrinkingSwitchRank_lt_add_one hC M
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hRank
  have hmul := mul_le_mul_of_nonneg_left hlogBound hC
  calc
    (shrinkingSwitchRank C M : ℝ) ≤
        C * Real.log ((M : ℝ) + 2) + 1 := hswitch.le
    _ ≤ C * (2 * firstPassageEndpointRate * (L : ℝ)) + 1 := by
      linarith
    _ ≤ C * (2 * firstPassageEndpointRate * (L : ℝ)) + (L : ℝ) := by
      linarith
    _ = (2 * C * firstPassageEndpointRate + 1) * (L : ℝ) := by ring
end FirstPassageLinearTransport

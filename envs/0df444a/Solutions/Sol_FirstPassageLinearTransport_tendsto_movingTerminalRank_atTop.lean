-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_movingTerminalRank_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:03:21.700184+00:00
-- url     : https://prove2.me/submissions/1d098eb2-ff70-457e-8784-697bfb1dd0a8

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEntropyGap_pos
import Theorems.Thm_FirstPassageLinearTransport_movingRankBuffer_eq
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
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop) :
    Tendsto (movingTerminalRank A) atTop atTop := by
  rw [tendsto_atTop] at hbuffer ⊢
  intro N
  have hbuf := hbuffer (firstPassageEntropyGap * (N : ℝ))
  filter_upwards [hbuf, eventually_ge_atTop (1 : ℕ)] with M hbuf hM
  let x : ℝ := (M : ℝ) + 2
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hlogb0 : 0 ≤ Real.logb 2 x :=
    Real.logb_nonneg (by norm_num) hx1
  have hlog1 : 1 ≤ Real.log ((M : ℝ) + 3) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hloglog0 : 0 ≤ Real.logb 2 (Real.log ((M : ℝ) + 3)) :=
    Real.logb_nonneg (by norm_num) hlog1
  have hupper : movingRankBuffer A M ≤
      firstPassageEntropyGap * (movingTerminalRank A M : ℝ) := by
    rw [movingRankBuffer_eq]
    linarith
  have hcast : (N : ℝ) ≤ (movingTerminalRank A M : ℝ) := by
    have hmul : firstPassageEntropyGap * (N : ℝ) ≤
        firstPassageEntropyGap * (movingTerminalRank A M : ℝ) :=
      hbuf.trans hupper
    exact le_of_mul_le_mul_left hmul firstPassageEntropyGap_pos
  exact_mod_cast hcast
end FirstPassageLinearTransport

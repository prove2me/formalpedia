-- Prove2me | solution 1 for FirstPassageLinearTransport.two_rpow_neg_movingRankBuffer_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:58:40.393122+00:00
-- url     : https://prove2.me/submissions/77b68dbb-5551-47be-8c6a-782583a48ce4

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointRate_eq_entropyGap_mul_logTwo
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
    (A : ℕ → ℝ) (M : ℕ) :
    (2 : ℝ) ^ (-(movingRankBuffer A M)) =
      Real.sqrt ((M : ℝ) + 2) * Real.log ((M : ℝ) + 3) *
        Real.exp (-(firstPassageEndpointRate *
          (movingTerminalRank A M : ℝ))) := by
  let x : ℝ := (M : ℝ) + 2
  let y : ℝ := Real.log ((M : ℝ) + 3)
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by
    dsimp [y]
    apply Real.log_pos
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have htwo : 0 < (2 : ℝ) := by norm_num
  have hfirst :
      (2 : ℝ) ^ (-(firstPassageEntropyGap *
          (movingTerminalRank A M : ℝ))) =
        Real.exp (-(firstPassageEndpointRate *
          (movingTerminalRank A M : ℝ))) := by
    rw [Real.rpow_def_of_pos htwo]
    rw [firstPassageEndpointRate_eq_entropyGap_mul_logTwo]
    congr 1
    ring
  have hsecond :
      (2 : ℝ) ^ ((1 / 2 : ℝ) * Real.logb 2 x) = Real.sqrt x := by
    rw [show (1 / 2 : ℝ) * Real.logb 2 x =
        Real.logb 2 x * (1 / 2 : ℝ) by ring,
      Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hx,
      Real.sqrt_eq_rpow]
  have hthird : (2 : ℝ) ^ (Real.logb 2 y) = y := by
    exact Real.rpow_logb (by norm_num) (by norm_num) hy
  rw [movingRankBuffer_eq]
  rw [show -(firstPassageEntropyGap * movingTerminalRank A M -
        (1 / 2) * Real.logb 2 ((M : ℝ) + 2) -
        Real.logb 2 (Real.log ((M : ℝ) + 3))) =
      -(firstPassageEntropyGap * (movingTerminalRank A M : ℝ)) +
        (1 / 2) * Real.logb 2 x + Real.logb 2 y by
      dsimp [x, y]
      ring,
    Real.rpow_add htwo, Real.rpow_add htwo, hfirst, hsecond, hthird]
  dsimp [x, y]
  ring
end FirstPassageLinearTransport

-- Prove2me | solution 1 for FirstPassageLinearTransport.sharp_timeout_scalar_le_buffer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:59:49.245959+00:00
-- url     : https://prove2.me/submissions/476c6062-6479-4485-b910-531f1c0260f3

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointRate_eq_entropyGap_mul_logTwo
import Theorems.Thm_FirstPassageLinearTransport_sharpMovingRankBuffer_eq
import Theorems.Thm_FirstPassageLinearTransport_two_rpow_neg_sharpMovingRankBuffer_eq
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointRate_pos
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
    {A : ℕ → ℝ} {M : ℕ}
    (hbuf : 0 ≤ sharpMovingRankBuffer A M)
    (hL : 1 ≤ movingTerminalRank A M) :
    Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
        (1 / Real.sqrt (movingTerminalRank A M)) *
        Real.exp (-(firstPassageEndpointRate *
          (movingTerminalRank A M : ℝ))) ≤
      Real.sqrt (2 * firstPassageEndpointRate) *
        (2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) := by
  let x : ℝ := (M : ℝ) + 2
  let L : ℕ := movingTerminalRank A M
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hL1 : 1 ≤ L := by simpa [L] using hL
  have hLR : 0 < (L : ℝ) := by positivity
  have hlogbBound : Real.logb 2 x ≤
      2 * firstPassageEntropyGap * (L : ℝ) := by
    rw [sharpMovingRankBuffer_eq] at hbuf
    dsimp [x, L] at hbuf ⊢
    linarith
  have hlogIdentity : Real.log x = Real.log 2 * Real.logb 2 x := by
    simp [Real.logb]
    field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hlogBound : Real.log x ≤
      2 * firstPassageEndpointRate * (L : ℝ) := by
    rw [hlogIdentity, firstPassageEndpointRate_eq_entropyGap_mul_logTwo]
    have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    nlinarith [mul_le_mul_of_nonneg_left hlogbBound hlog2]
  have hsqrtLog : Real.sqrt (Real.log x) ≤
      Real.sqrt (2 * firstPassageEndpointRate * (L : ℝ)) :=
    Real.sqrt_le_sqrt hlogBound
  have hsqrtXL : Real.sqrt (x * Real.log x) ≤
      Real.sqrt x * Real.sqrt (2 * firstPassageEndpointRate * (L : ℝ)) := by
    rw [Real.sqrt_mul hx0.le]
    gcongr
  have hsqrtSplit :
      Real.sqrt (2 * firstPassageEndpointRate * (L : ℝ)) =
        Real.sqrt (2 * firstPassageEndpointRate) * Real.sqrt L := by
    rw [Real.sqrt_mul
      (mul_nonneg (by norm_num) firstPassageEndpointRate_pos.le)]
  have hcancel : Real.sqrt L * (1 / Real.sqrt L) = 1 := by
    field_simp [Real.sqrt_ne_zero'.2 hLR]
  have hcore : Real.sqrt (x * Real.log x) * (1 / Real.sqrt L) ≤
      Real.sqrt (2 * firstPassageEndpointRate) * Real.sqrt x := by
    calc
      _ ≤ (Real.sqrt x *
          Real.sqrt (2 * firstPassageEndpointRate * (L : ℝ))) *
          (1 / Real.sqrt L) := by
        gcongr
      _ = Real.sqrt (2 * firstPassageEndpointRate) * Real.sqrt x := by
        rw [hsqrtSplit]
        rw [show Real.sqrt x *
            (Real.sqrt (2 * firstPassageEndpointRate) * Real.sqrt L) *
              (1 / Real.sqrt L) =
            Real.sqrt (2 * firstPassageEndpointRate) * Real.sqrt x *
              (Real.sqrt L * (1 / Real.sqrt L)) by ring,
          hcancel]
        ring
  have hexp0 : 0 ≤ Real.exp (-(firstPassageEndpointRate * (L : ℝ))) :=
    Real.exp_pos _ |>.le
  calc
    Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
          (1 / Real.sqrt (movingTerminalRank A M)) *
          Real.exp (-(firstPassageEndpointRate *
            (movingTerminalRank A M : ℝ))) =
        (Real.sqrt (x * Real.log x) * (1 / Real.sqrt L)) *
          Real.exp (-(firstPassageEndpointRate * (L : ℝ))) := by rfl
    _ ≤ (Real.sqrt (2 * firstPassageEndpointRate) * Real.sqrt x) *
          Real.exp (-(firstPassageEndpointRate * (L : ℝ))) := by
      exact mul_le_mul_of_nonneg_right hcore hexp0
    _ = Real.sqrt (2 * firstPassageEndpointRate) *
          (2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) := by
      rw [two_rpow_neg_sharpMovingRankBuffer_eq]
      ring
end FirstPassageLinearTransport

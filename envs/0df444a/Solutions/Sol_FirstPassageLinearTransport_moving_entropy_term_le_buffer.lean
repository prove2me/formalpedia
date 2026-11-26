-- Prove2me | solution 1 for FirstPassageLinearTransport.moving_entropy_term_le_buffer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:35.049139+00:00
-- url     : https://prove2.me/submissions/7a6fede7-b97c-4498-b648-b547d8602758

import Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTailAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeSupportScalars
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAsymptotics
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
import Theorems.Thm_FirstPassageLinearTransport_movingTerminalRank_lt_add_one
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_two_rpow_neg_movingRankBuffer_eq
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
    {A : ℕ → ℝ} {Amax D : ℝ} {M : ℕ}
    (hAmax : 0 < Amax) (hD : 0 < D)
    (hA0 : 0 ≤ A M) (hAupper : A M ≤ Amax)
    (hL : 1 ≤ movingTerminalRank A M) :
    Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
        Real.sqrt (movingTerminalRank A M) *
        Real.exp (-((firstPassageEndpointRate -
          D / (movingTerminalRank A M : ℝ)) *
            ((movingTerminalRank A M - 1 : ℕ) : ℝ))) ≤
      (Real.sqrt (Amax / Real.log 2 + 1) *
          Real.exp (firstPassageEndpointRate + D)) *
        ((2 : ℝ) ^ (-(movingRankBuffer A M))) := by
  let x : ℝ := (M : ℝ) + 2
  let y : ℝ := Real.log ((M : ℝ) + 3)
  let L : ℕ := movingTerminalRank A M
  let K : ℝ := Amax / Real.log 2 + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : 0 < x := by dsimp [x]; positivity
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hx1 : 1 ≤ x := by
    dsimp [x]
    linarith
  have hy1 : 1 ≤ y := by
    dsimp [y]
    apply (Real.le_log_iff_exp_le (by linarith)).2
    have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    linarith
  have hy0 : 0 ≤ y := zero_le_one.trans hy1
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlogxy : Real.log x ≤ y := by
    dsimp [x, y]
    apply Real.strictMonoOn_log.monotoneOn
    · exact (by linarith : 0 < (M : ℝ) + 2)
    · exact (by linarith : 0 < (M : ℝ) + 3)
    · linarith
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hLnat : 1 ≤ L := by simpa [L] using hL
  have hLr : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hLupper : (L : ℝ) ≤ K * y := by
    have hceil := movingTerminalRank_lt_add_one hA0
    have hAlog : A M * Real.logb 2 x ≤
        (Amax / Real.log 2) * y := by
      rw [Real.logb]
      have hAlogx : A M * Real.log x ≤ Amax * y := by
        calc
          A M * Real.log x ≤ Amax * Real.log x := by gcongr
          _ ≤ Amax * y := by gcongr
      calc
        A M * (Real.log x / Real.log 2) =
            (A M * Real.log x) / Real.log 2 := by ring
        _ ≤ (Amax * y) / Real.log 2 :=
          (div_le_div_iff_of_pos_right hlog2).2 hAlogx
        _ = (Amax / Real.log 2) * y := by ring
    exact (hceil.trans_le (by
      calc
        A M * Real.logb 2 x + 1 ≤
            (Amax / Real.log 2) * y + y := add_le_add hAlog hy1
        _ = K * y := by dsimp [K]; ring)).le
  have hsqrtPair : Real.sqrt (Real.log x) * Real.sqrt L ≤
      Real.sqrt K * y := by
    rw [← Real.sqrt_mul hlogx0]
    have hprod : Real.log x * (L : ℝ) ≤ K * y ^ 2 := by
      calc
        Real.log x * (L : ℝ) ≤ y * (K * y) := by gcongr
        _ = K * y ^ 2 := by ring
    have hsqrt := Real.sqrt_le_sqrt hprod
    have hK0 : 0 ≤ K := hK.le
    rw [Real.sqrt_mul hK0, Real.sqrt_sq hy0] at hsqrt
    exact hsqrt
  have hsqrtSplit :
      Real.sqrt (x * Real.log x) = Real.sqrt x * Real.sqrt (Real.log x) := by
    rw [Real.sqrt_mul hx.le]
  have hexponent :
      -((firstPassageEndpointRate - D / (L : ℝ)) *
          ((L - 1 : ℕ) : ℝ)) ≤
        -(firstPassageEndpointRate * (L : ℝ)) +
          firstPassageEndpointRate + D := by
    have hsubCast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
      rw [Nat.cast_sub hLnat]
      norm_num
    have hfrac : D * (((L : ℝ) - 1) / (L : ℝ)) ≤ D := by
      have hratio : ((L : ℝ) - 1) / (L : ℝ) ≤ 1 := by
        rw [div_le_one hLr]
        linarith
      simpa using mul_le_mul_of_nonneg_left hratio hD.le
    rw [hsubCast]
    calc
      -((firstPassageEndpointRate - D / (L : ℝ)) * ((L : ℝ) - 1)) =
          -(firstPassageEndpointRate * (L : ℝ)) +
            firstPassageEndpointRate +
              D * (((L : ℝ) - 1) / (L : ℝ)) := by ring
      _ ≤ _ := by linarith
  have hexp := Real.exp_le_exp.mpr hexponent
  have hbuffer := two_rpow_neg_movingRankBuffer_eq A M
  calc
    Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
        Real.sqrt (movingTerminalRank A M) *
        Real.exp (-((firstPassageEndpointRate -
          D / (movingTerminalRank A M : ℝ)) *
            ((movingTerminalRank A M - 1 : ℕ) : ℝ))) =
      (Real.sqrt x *
        (Real.sqrt (Real.log x) * Real.sqrt L)) *
        Real.exp (-((firstPassageEndpointRate - D / (L : ℝ)) *
          ((L - 1 : ℕ) : ℝ))) := by
        dsimp [x, L]
        rw [hsqrtSplit]
        ring
    _ ≤ (Real.sqrt x * (Real.sqrt K * y)) *
        Real.exp (-(firstPassageEndpointRate * (L : ℝ)) +
          firstPassageEndpointRate + D) := by gcongr
    _ = (Real.sqrt K * Real.exp (firstPassageEndpointRate + D)) *
        (Real.sqrt x * y *
          Real.exp (-(firstPassageEndpointRate * (L : ℝ)))) := by
      rw [show -(firstPassageEndpointRate * (L : ℝ)) +
          firstPassageEndpointRate + D =
        (firstPassageEndpointRate + D) +
          -(firstPassageEndpointRate * (L : ℝ)) by ring,
        Real.exp_add]
      ring
    _ = (Real.sqrt (Amax / Real.log 2 + 1) *
          Real.exp (firstPassageEndpointRate + D)) *
        ((2 : ℝ) ^ (-(movingRankBuffer A M))) := by
      rw [hbuffer]
end FirstPassageLinearTransport

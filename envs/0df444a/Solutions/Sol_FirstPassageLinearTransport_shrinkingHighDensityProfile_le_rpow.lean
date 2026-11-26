-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingHighDensityProfile_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:26:14.568391+00:00
-- url     : https://prove2.me/submissions/a6747e6f-541a-4cd9-860d-19c0fbd473cb

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTailAsymptotics
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
import Theorems.Thm_FirstPassageLinearTransport_quadraticWindowShellConstant_pos
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_shrinkingSwitchRank_lower
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
    (P : ShrinkingBarrierRunData) (C : ℝ) (M : ℕ) :
    shrinkingHighDensityProfile P C M ≤
      (1 + quadraticWindowShellConstant) *
        (((M : ℝ) + 2) ^
          (-min (C * Real.log 2) (maximalBarrierC0 * P.D ^ 2))) := by
  let x : ℝ := (M : ℝ) + 2
  let p := min (C * Real.log 2) (maximalBarrierC0 * P.D ^ 2)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hswitch := shrinkingSwitchRank_lower C M
  have hboundary :
      Real.exp (-(Real.log 2 * (shrinkingSwitchRank C M : ℝ))) ≤
        x ^ (-(C * Real.log 2)) := by
    rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left hswitch hlog2.le
    dsimp [x]
    linarith
  have hbarrier :
      Real.exp (-(maximalBarrierC0 * P.D ^ 2 * Real.log x)) =
        x ^ (-(maximalBarrierC0 * P.D ^ 2)) := by
    rw [Real.rpow_def_of_pos hx0]
    ring_nf
  have hpLeft : p ≤ C * Real.log 2 := min_le_left _ _
  have hpRight : p ≤ maximalBarrierC0 * P.D ^ 2 := min_le_right _ _
  have hboundaryP : x ^ (-(C * Real.log 2)) ≤ x ^ (-p) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hbarrierP : x ^ (-(maximalBarrierC0 * P.D ^ 2)) ≤ x ^ (-p) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hquad0 : 0 ≤ quadraticWindowShellConstant :=
    quadraticWindowShellConstant_pos.le
  calc
    shrinkingHighDensityProfile P C M ≤
        x ^ (-(C * Real.log 2)) +
          quadraticWindowShellConstant *
            x ^ (-(maximalBarrierC0 * P.D ^ 2)) := by
      unfold shrinkingHighDensityProfile
      rw [hbarrier]
      exact add_le_add hboundary le_rfl
    _ ≤ x ^ (-p) + quadraticWindowShellConstant * x ^ (-p) := by
      exact add_le_add hboundaryP
        (mul_le_mul_of_nonneg_left hbarrierP hquad0)
    _ = (1 + quadraticWindowShellConstant) * x ^ (-p) := by ring
end FirstPassageLinearTransport

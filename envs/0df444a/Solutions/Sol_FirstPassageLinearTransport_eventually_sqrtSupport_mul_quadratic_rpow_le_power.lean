-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_sqrtSupport_mul_quadratic_rpow_le_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:44:55.7741+00:00
-- url     : https://prove2.me/submissions/dd478c6c-1bfd-414c-8197-164c0bf3d47e

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTailAsymptotics
import Theorems.Thm_FirstPassageLinearTransport_eventually_sqrt_mul_log_rpow_le
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
    {p kappa : ℝ} (hkappa : kappa < p - 5 / 2) :
    ∀ᶠ M : ℕ in atTop,
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
          (((M : ℝ) + 1) ^ 2 * (((M : ℝ) + 2) ^ (-p))) ≤
        ((M : ℝ) + 2) ^ (-kappa) := by
  have hbase := eventually_sqrt_mul_log_rpow_le
    (p := p - 2) (kappa := kappa) (by linarith)
  filter_upwards [hbase] with M hbase
  let x : ℝ := (M : ℝ) + 2
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hquad : ((M : ℝ) + 1) ^ 2 ≤ x ^ (2 : ℕ) := by
    gcongr
    dsimp [x]
    linarith
  have hpow0 : 0 ≤ x ^ (-p) := Real.rpow_nonneg hx0.le _
  have hsqrt0 : 0 ≤ Real.sqrt (x * Real.log x) := Real.sqrt_nonneg _
  have hrewrite : x ^ (2 : ℕ) * x ^ (-p) = x ^ (-(p - 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
    congr 1
    ring
  calc
    Real.sqrt (x * Real.log x) *
        (((M : ℝ) + 1) ^ 2 * x ^ (-p)) ≤
      Real.sqrt (x * Real.log x) * (x ^ (2 : ℕ) * x ^ (-p)) := by
        gcongr
    _ = Real.sqrt (x * Real.log x) * x ^ (-(p - 2)) := by rw [hrewrite]
    _ ≤ x ^ (-kappa) := by simpa [x] using hbase
end FirstPassageLinearTransport

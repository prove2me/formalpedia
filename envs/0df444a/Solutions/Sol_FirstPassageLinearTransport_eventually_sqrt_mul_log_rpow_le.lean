-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_sqrt_mul_log_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:43:22.722946+00:00
-- url     : https://prove2.me/submissions/b7a43869-2b92-4ee0-8e22-cf90fe04bd86

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
    {p kappa : ℝ} (hkappa : kappa < p - 1 / 2) :
    ∀ᶠ M : ℕ in atTop,
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
          (((M : ℝ) + 2) ^ (-p)) ≤
        ((M : ℝ) + 2) ^ (-kappa) := by
  let eps := p - 1 / 2 - kappa
  have heps : 0 < eps := by dsimp [eps]; linarith
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop (s := eps) (1 / 2 : ℝ) heps).bound
      (by norm_num : (0 : ℝ) < 1)
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hsmall := hxT.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with M hsmall hM
  let x : ℝ := (M : ℝ) + 2
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxeps0 : 0 ≤ x ^ eps := Real.rpow_nonneg hx0.le _
  have hlogHalf0 : 0 ≤ Real.log x ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg hlog0 _
  rw [Real.norm_eq_abs, abs_of_nonneg hlogHalf0,
    Real.norm_eq_abs, abs_of_nonneg hxeps0, one_mul] at hsmall
  have hsqrtFactor :
      Real.sqrt (x * Real.log x) ≤ x ^ (1 / 2 : ℝ) * x ^ eps := by
    rw [Real.sqrt_mul hx0.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hx0.le _)
  calc
    Real.sqrt (x * Real.log x) * x ^ (-p) ≤
        (x ^ (1 / 2 : ℝ) * x ^ eps) * x ^ (-p) :=
      mul_le_mul_of_nonneg_right hsqrtFactor (Real.rpow_nonneg hx0.le _)
    _ = x ^ (-kappa) := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      congr 1
      dsimp [eps]
      ring
end FirstPassageLinearTransport

-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_shrinkingSwitchRank_lt_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:36:51.574621+00:00
-- url     : https://prove2.me/submissions/f25a3e5c-bb57-444f-9ce4-0d85b0c7506b

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Theorems.Thm_FirstPassageLinearTransport_shrinkingSwitchRank_lt_add_one
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFeasibleTimes
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop, shrinkingSwitchRank C M < M := by
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hsmallReal := Real.isLittleO_log_id_atTop.bound
    (show (0 : ℝ) < 1 / (2 * (C + 1)) by
      have : 0 < C + 1 := by linarith
      positivity)
  have hsmall := hxT.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop (5 : ℕ)] with M hsmall hM
  have hx0 : 0 ≤ (M : ℝ) + 2 := by positivity
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hx1 : (1 : ℝ) ≤ (M : ℝ) + 2 := by
    linarith
  have hlog0 : 0 ≤ Real.log ((M : ℝ) + 2) := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, abs_of_nonneg hlog0] at hsmall
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0] at hsmall
  have hswitch := shrinkingSwitchRank_lt_add_one hC M
  have hreal : (shrinkingSwitchRank C M : ℝ) < (M : ℝ) := by
    calc
      (shrinkingSwitchRank C M : ℝ) <
          C * Real.log ((M : ℝ) + 2) + 1 := hswitch
      _ ≤ C * ((M : ℝ) + 2) / (2 * (C + 1)) + 1 := by
        have hmul := mul_le_mul_of_nonneg_left hsmall hC
        calc
          C * Real.log ((M : ℝ) + 2) + 1 ≤
              C * (1 / (2 * (C + 1)) * ((M : ℝ) + 2)) + 1 := by
            linarith
          _ = C * ((M : ℝ) + 2) / (2 * (C + 1)) + 1 := by ring
      _ < (M : ℝ) := by
        have hMR : (5 : ℝ) ≤ M := by exact_mod_cast hM
        have hC1 : 0 < C + 1 := by linarith
        have hfrac : C / (2 * (C + 1)) ≤ (1 / 2 : ℝ) := by
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (C + 1))).2
          nlinarith
        calc
          C * ((M : ℝ) + 2) / (2 * (C + 1)) + 1 =
              (C / (2 * (C + 1))) * ((M : ℝ) + 2) + 1 := by ring
          _ ≤ (1 / 2 : ℝ) * ((M : ℝ) + 2) + 1 := by gcongr
          _ < (M : ℝ) := by linarith
  exact_mod_cast hreal
end FirstPassageLinearTransport

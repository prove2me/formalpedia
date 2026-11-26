-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_shrinkingHorizon_lt_shellClock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:48.509613+00:00
-- url     : https://prove2.me/submissions/6340aea8-0f31-435e-b07f-b87a8c90ac44

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
    {rHi rLo : ℚ} {C c : ℝ}
    (hrHi1 : rHi < 1) (hrLo1 : rLo < 1)
    (hC : 0 ≤ C)
    (hlead : 1 / (1 - (rHi : ℝ)) < c * Real.log 2) :
    ∀ᶠ M : ℕ in atTop,
      (twoRegimeHorizon rHi rLo (shrinkingSwitchRank C M) M : ℝ) <
        c * (M : ℝ) * Real.log 2 := by
  let dHi : ℝ := 1 - (rHi : ℝ)
  let dLo : ℝ := 1 - (rLo : ℝ)
  have hdHi : 0 < dHi := by
    dsimp [dHi]
    have h : (rHi : ℝ) < 1 := by exact_mod_cast hrHi1
    linarith
  have hdLo : 0 < dLo := by
    dsimp [dLo]
    have h : (rLo : ℝ) < 1 := by exact_mod_cast hrLo1
    linarith
  let g : ℝ := c * Real.log 2 - 1 / dHi
  have hg : 0 < g := by dsimp [g, dHi]; linarith
  let q : ℝ := g * dLo / (4 * (C + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hsmall := hxT.eventually (Real.isLittleO_log_id_atTop.bound hq)
  have hlinT : Tendsto (fun M : ℕ => (3 * g / 4) * (M : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have hlarge : ∀ᶠ M : ℕ in atTop,
      g / 2 + 1 / dLo + 1 < (3 * g / 4) * (M : ℝ) := by
    filter_upwards [(tendsto_atTop.1 hlinT) (g / 2 + 1 / dLo + 2)]
      with M hM
    linarith
  filter_upwards [hsmall, hlarge] with M hsmall hlarge
  have hx0 : 0 ≤ (M : ℝ) + 2 := by positivity
  have hx1 : 1 ≤ (M : ℝ) + 2 := by
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hlog0 : 0 ≤ Real.log ((M : ℝ) + 2) := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, abs_of_nonneg hlog0] at hsmall
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0] at hsmall
  have hSdiv :
      (shrinkingSwitchRank C M : ℝ) / dLo <
        g / 4 * ((M : ℝ) + 2) + 1 / dLo := by
    have hS := shrinkingSwitchRank_lt_add_one hC M
    have hCd : C / (C + 1) ≤ 1 := by
      apply (div_le_one (by linarith)).2
      linarith
    have hmain : C * Real.log ((M : ℝ) + 2) ≤
        g * dLo / 4 * ((M : ℝ) + 2) := by
      have hmul := mul_le_mul_of_nonneg_left hsmall hC
      calc
        C * Real.log ((M : ℝ) + 2) ≤ C * (q * ((M : ℝ) + 2)) := hmul
        _ = (g * dLo / 4) * (C / (C + 1)) * ((M : ℝ) + 2) := by
          dsimp [q]
          field_simp [ne_of_gt (by linarith : (0 : ℝ) < C + 1)]
        _ ≤ (g * dLo / 4) * 1 * ((M : ℝ) + 2) := by gcongr
        _ = g * dLo / 4 * ((M : ℝ) + 2) := by ring
    calc
      (shrinkingSwitchRank C M : ℝ) / dLo <
          (C * Real.log ((M : ℝ) + 2) + 1) / dLo :=
        (div_lt_div_iff_of_pos_right hdLo).2 hS
      _ ≤ (g * dLo / 4 * ((M : ℝ) + 2) + 1) / dLo := by gcongr
      _ = g / 4 * ((M : ℝ) + 2) + 1 / dLo := by
        field_simp [ne_of_gt hdLo]
  have hbudget0 : 0 ≤ (M : ℝ) / dHi +
      (shrinkingSwitchRank C M : ℝ) / dLo := by positivity
  have hceil :
      (twoRegimeHorizon rHi rLo (shrinkingSwitchRank C M) M : ℝ) <
        (M : ℝ) / dHi + (shrinkingSwitchRank C M : ℝ) / dLo + 1 := by
    simpa [twoRegimeHorizon, dHi, dLo] using Nat.ceil_lt_add_one hbudget0
  have hid : 1 / dHi + g = c * Real.log 2 := by dsimp [g]; ring
  calc
    _ < (M : ℝ) / dHi + (shrinkingSwitchRank C M : ℝ) / dLo + 1 := hceil
    _ < (M : ℝ) / dHi +
        (g / 4 * ((M : ℝ) + 2) + 1 / dLo) + 1 := by linarith
    _ < (1 / dHi + g) * (M : ℝ) := by
      calc
        (M : ℝ) / dHi +
            (g / 4 * ((M : ℝ) + 2) + 1 / dLo) + 1 =
          (1 / dHi) * (M : ℝ) +
            (g / 4 * ((M : ℝ) + 2) + 1 / dLo) + 1 := by ring
        _ < (1 / dHi + g) * (M : ℝ) := by nlinarith
    _ = c * (M : ℝ) * Real.log 2 := by rw [hid]; ring
end FirstPassageLinearTransport

-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_shrinkingSwitchRank_envelope_le_shellMargin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:38.901118+00:00
-- url     : https://prove2.me/submissions/0a2e92b7-b573-4927-96f8-c06fce65e561

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
    {C eta beta : ℝ} (hC : 0 ≤ C) (heta : 0 ≤ eta)
    (hbeta : 0 < beta) :
    ∀ᶠ M : ℕ in atTop,
      (shrinkingSwitchRank C M : ℝ) * (1 + eta) ≤ beta * (M : ℝ) := by
  let q := beta / (2 * (C + 1) * (1 + eta))
  have hq : 0 < q := by dsimp [q]; positivity
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hsmall := hxT.eventually (Real.isLittleO_log_id_atTop.bound hq)
  have hlarge : ∀ᶠ M : ℕ in atTop,
      2 * (1 + eta) + 2 * beta ≤ beta * (M : ℝ) := by
    have ht : Tendsto (fun M : ℕ => beta * (M : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hbeta
    exact (tendsto_atTop.1 ht) _
  filter_upwards [hsmall, hlarge] with M hsmall hlarge
  have hx0 : 0 ≤ (M : ℝ) + 2 := by positivity
  have hx1 : 1 ≤ (M : ℝ) + 2 := by
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hlog0 : 0 ≤ Real.log ((M : ℝ) + 2) := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, abs_of_nonneg hlog0] at hsmall
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0] at hsmall
  have hS := shrinkingSwitchRank_lt_add_one hC M
  have hCfrac : C / (C + 1) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  have hlogTerm : C * Real.log ((M : ℝ) + 2) * (1 + eta) ≤
      beta / 2 * ((M : ℝ) + 2) := by
    have hmul := mul_le_mul_of_nonneg_left hsmall hC
    calc
      C * Real.log ((M : ℝ) + 2) * (1 + eta) ≤
          C * (q * ((M : ℝ) + 2)) * (1 + eta) := by gcongr
      _ = beta / 2 * (C / (C + 1)) * ((M : ℝ) + 2) := by
        dsimp [q]
        field_simp [ne_of_gt (by linarith : (0 : ℝ) < C + 1),
          ne_of_gt (by linarith : (0 : ℝ) < 1 + eta)]
      _ ≤ beta / 2 * 1 * ((M : ℝ) + 2) := by gcongr
      _ = beta / 2 * ((M : ℝ) + 2) := by ring
  calc
    (shrinkingSwitchRank C M : ℝ) * (1 + eta) ≤
        (C * Real.log ((M : ℝ) + 2) + 1) * (1 + eta) := by gcongr
    _ ≤ beta / 2 * ((M : ℝ) + 2) + (1 + eta) := by
      nlinarith
    _ ≤ beta * (M : ℝ) := by nlinarith
end FirstPassageLinearTransport

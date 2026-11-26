-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_rawClockStage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:40.738422+00:00
-- url     : https://prove2.me/submissions/aa304fe7-e89e-48bd-92dd-ffa432b60e0c

import Definitions.Def_FirstPassageLinearTransport_RawClockBudget
import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_clockLeadingLt6953
import Theorems.Thm_FirstPassageLinearTransport_exists_headlineScalars
import Theorems.Thm_FirstPassageLinearTransport_exists_stageSetup
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ (h : HeadlineScalars delta) (eta : ℝ) (_p : StageSetup h.r eta),
      eta < h.r - a0 ∧ rawClockLeading h.r eta < (261 / 25 : ℝ) := by
  let h : HeadlineScalars delta :=
    Classical.choice (exists_headlineScalars hdelta0 hdelta1)
  let base := (3 / (2 * Real.log 2)) / (1 - h.r)
  let gap := (261 / 25 : ℝ) - base
  have hr1 : h.r < 1 := h.r_lt_one
  have hden : 0 < 1 - h.r := sub_pos.mpr hr1
  have hshortcut := clockLeadingLt6953 h.r_lt_clock
  have hbase : base < (261 / 25 : ℝ) := by
    have hscaled := mul_lt_mul_of_pos_left hshortcut (by norm_num :
      (0 : ℝ) < 3 / 2)
    have hreform :
        base = 3 / 2 * (1 / ((1 - h.r) * Real.log 2)) := by
      dsimp [base]
      field_simp [hden.ne', (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
    rw [hreform]
    exact hscaled.trans (by norm_num)
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let eta := min ((h.r - a0) / 2)
    (gap * (1 - h.r) * Real.log 3 / 2)
  have heta0 : 0 < eta := by
    dsimp [eta]
    exact lt_min (by linarith [h.a0_lt_r]) (by positivity)
  have hetaGap : eta < h.r - a0 := by
    have hle : eta ≤ (h.r - a0) / 2 := by
      dsimp [eta]
      exact min_le_left _ _
    linarith [h.a0_lt_r]
  have hetaBudget :
      eta ≤ gap * (1 - h.r) * Real.log 3 / 2 := by
    dsimp [eta]
    exact min_le_right _ _
  let p : StageSetup h.r eta := Classical.choice
    (exists_stageSetup h.a0_lt_r h.r_lt_one heta0 hetaGap)
  have hextra :
      (eta / Real.log 3) / (1 - h.r) ≤ gap / 2 := by
    apply (div_le_iff₀ hden).2
    apply (div_le_iff₀ hlog3).2
    nlinarith
  refine ⟨h, eta, p, hetaGap, ?_⟩
  unfold rawClockLeading
  have hsplit :
      (3 / (2 * Real.log 2) + eta / Real.log 3) / (1 - h.r) =
        base + (eta / Real.log 3) / (1 - h.r) := by
    dsimp [base]
    ring
  rw [hsplit]
  dsimp [gap] at hextra
  linarith
end FirstPassageLinearTransport

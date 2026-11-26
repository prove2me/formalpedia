-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_rawClockHeightStageOfHeadline
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:39:02.961601+00:00
-- url     : https://prove2.me/submissions/02d9c585-0698-4d5e-97b4-b9226e09d55e

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Theorems.Thm_FirstPassageLinearTransport_a0_pos
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_clockLeadingLt6953
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
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
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
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {delta : ℝ} (h : HeadlineScalars delta) :
    ∃ (eta : ℝ) (_p : StageSetup h.r eta),
      eta < h.r - a0 ∧
      rawClockLeading h.r eta < (261 / 25 : ℝ) ∧
      h.r * (1 + eta) < 1 := by
  let base := (3 / (2 * Real.log 2)) / (1 - h.r)
  let gap := (261 / 25 : ℝ) - base
  have hr0 : 0 < h.r := a0_pos.trans h.a0_lt_r
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
  let etaRaw := min ((h.r - a0) / 2)
    (gap * (1 - h.r) * Real.log 3 / 2)
  have hetaRaw0 : 0 < etaRaw := by
    dsimp [etaRaw]
    exact lt_min (by linarith [h.a0_lt_r]) (by positivity)
  let eta := min etaRaw ((1 - h.r) / (2 * h.r))
  have hcap0 : 0 < (1 - h.r) / (2 * h.r) :=
    div_pos hden (mul_pos (by norm_num) hr0)
  have heta0 : 0 < eta := by
    dsimp [eta]
    exact lt_min hetaRaw0 hcap0
  have hetaLeRaw : eta ≤ etaRaw := by
    dsimp [eta]
    exact min_le_left _ _
  have hetaRawGap : etaRaw < h.r - a0 := by
    have hle : etaRaw ≤ (h.r - a0) / 2 := by
      dsimp [etaRaw]
      exact min_le_left _ _
    linarith [h.a0_lt_r]
  have hetaGap : eta < h.r - a0 := hetaLeRaw.trans_lt hetaRawGap
  have hetaBudget :
      eta ≤ gap * (1 - h.r) * Real.log 3 / 2 := by
    exact hetaLeRaw.trans (by
      dsimp [etaRaw]
      exact min_le_right _ _)
  have hcap : eta ≤ (1 - h.r) / (2 * h.r) := by
    dsimp [eta]
    exact min_le_right _ _
  let p : StageSetup h.r eta := Classical.choice
    (exists_stageSetup h.a0_lt_r h.r_lt_one heta0 hetaGap)
  have hextra :
      (eta / Real.log 3) / (1 - h.r) ≤ gap / 2 := by
    apply (div_le_iff₀ hden).2
    apply (div_le_iff₀ hlog3).2
    nlinarith
  have hraw : rawClockLeading h.r eta < (261 / 25 : ℝ) := by
    unfold rawClockLeading
    have hsplit :
        (3 / (2 * Real.log 2) + eta / Real.log 3) / (1 - h.r) =
          base + (eta / Real.log 3) / (1 - h.r) := by
      dsimp [base]
      ring
    rw [hsplit]
    dsimp [gap] at hextra
    linarith
  have hre : h.r * (1 + eta) < 1 := by
    have hmul := mul_le_mul_of_nonneg_left hcap hr0.le
    have hform : h.r * ((1 - h.r) / (2 * h.r)) = (1 - h.r) / 2 := by
      field_simp [hr0.ne']
    rw [hform] at hmul
    nlinarith
  exact ⟨eta, p, hetaGap, hraw, hre⟩
end FirstPassageLinearTransport

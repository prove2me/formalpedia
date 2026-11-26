-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_rawClockHeightStage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:39:25.368146+00:00
-- url     : https://prove2.me/submissions/94bd1d3d-68fb-420a-a429-075e0ca2cb12

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
import Theorems.Thm_FirstPassageLinearTransport_exists_rawClockStage
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
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ (h : HeadlineScalars delta) (eta : ℝ) (_p : StageSetup h.r eta),
      eta < h.r - a0 ∧
      rawClockLeading h.r eta < (261 / 25 : ℝ) ∧
      h.r * (1 + eta) < 1 := by
  obtain ⟨h, eta0, _p0, heta0Gap, hraw0⟩ :=
    exists_rawClockStage hdelta0 hdelta1
  let eta := min eta0 ((1 - h.r) / (2 * h.r))
  have heta00 : 0 < eta0 := _p0.eta_pos
  have hr0 : 0 < h.r := a0_pos.trans h.a0_lt_r
  have hr1 : h.r < 1 := h.r_lt_one
  have hcap0 : 0 < (1 - h.r) / (2 * h.r) :=
    div_pos (sub_pos.mpr hr1) (mul_pos (by norm_num) hr0)
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min heta00 hcap0
  have hetaLe : eta ≤ eta0 := by
    dsimp [eta]
    exact min_le_left _ _
  have hetaGap : eta < h.r - a0 := hetaLe.trans_lt heta0Gap
  have hrawLe : rawClockLeading h.r eta ≤ rawClockLeading h.r eta0 := by
    unfold rawClockLeading
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hden : 0 < 1 - h.r := sub_pos.mpr hr1
    apply (div_le_div_iff_of_pos_right hden).2
    have hetaDiv : eta / Real.log 3 ≤ eta0 / Real.log 3 :=
      (div_le_div_iff_of_pos_right hlog3).2 hetaLe
    linarith
  have hcap : eta ≤ (1 - h.r) / (2 * h.r) := by
    dsimp [eta]
    exact min_le_right _ _
  have hre : h.r * (1 + eta) < 1 := by
    have hmul := mul_le_mul_of_nonneg_left hcap hr0.le
    have hform : h.r * ((1 - h.r) / (2 * h.r)) = (1 - h.r) / 2 := by
      field_simp [hr0.ne']
    rw [hform] at hmul
    nlinarith
  let p : StageSetup h.r eta := Classical.choice
    (exists_stageSetup h.a0_lt_r h.r_lt_one heta hetaGap)
  exact ⟨h, eta, p, hetaGap, hrawLe.trans_lt hraw0, hre⟩
end FirstPassageLinearTransport

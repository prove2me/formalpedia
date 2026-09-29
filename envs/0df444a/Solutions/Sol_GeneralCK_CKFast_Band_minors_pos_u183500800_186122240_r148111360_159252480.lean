-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u183500800_186122240_r148111360_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:36:40.882612+00:00
-- url     : https://prove2.me/submissions/24d1893e-df9b-4805-a374-efca7f69f4f8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/32, 71/320]`, `ρ ∈ [113/640, 243/1280]` by 16 cells of the computing
correction-band checker; each cell is kernel-checked in its own declaration. -/

theorem leaf_ok {U0 U1 R0 R1 : ℤ} {h : Hint} (hc : cellOK U0 U1 R0 R1 h = true) :
    treeOK U0 U1 R0 R1 (.leaf h) = true := by
  simpa only [treeOK] using hc

theorem join_su {U0 U1 R0 R1 m : ℤ} {l r : Tree} (hm : (decide (U0 ≤ m) && decide (m ≤ U1)) = true)
    (hl : treeOK U0 m R0 R1 l = true) (hr : treeOK m U1 R0 R1 r = true) :
    treeOK U0 U1 R0 R1 (.su m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

theorem join_sr {U0 U1 R0 R1 m : ℤ} {l r : Tree} (hm : (decide (R0 ≤ m) && decide (m ≤ R1)) = true)
    (hl : treeOK U0 U1 R0 m l = true) (hr : treeOK U0 U1 m R1 r = true) :
    treeOK U0 U1 R0 R1 (.sr m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

set_option maxRecDepth 100000 in
theorem cell0 : cellOK 183500800 184156160 148111360 150896640 ⟨⟨68649206905, 68649206913⟩, ⟨66564352264, 70751949780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 184156160 184811520 148111360 150896640 ⟨⟨68359272962, 68359272970⟩, ⟨66280763604, 70455580160⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 183500800 184156160 150896640 153681920 ⟨⟨69862540214, 69862540222⟩, ⟨67772849816, 71970111874⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 184156160 184811520 150896640 153681920 ⟨⟨69567975120, 69567975128⟩, ⟨67484642793, 71669098696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 184811520 185466880 148111360 150896640 ⟨⟨68070513455, 68070513457⟩, ⟨65998312322, 70160422763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 185466880 186122240 148111360 150896640 ⟨⟨67782918344, 67782918351⟩, ⟨65716988725, 69866467203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 184811520 185466880 150896640 153681920 ⟨⟨69274597737, 69274597740⟩, ⟨67197586428, 71369311002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 185466880 186122240 150896640 153681920 ⟨⟨68982397942, 68982397948⟩, ⟨66911670949, 71070738326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 183500800 184156160 153681920 156467200 ⟨⟨71073754862, 71073754870⟩, ⟨68979243915, 73186139962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 184156160 184811520 153681920 156467200 ⟨⟨70774582324, 70774582330⟩, ⟨68686441995, 72880507172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 183500800 184156160 156467200 159252480 ⟨⟨72282864430, 72282864436⟩, ⟨70183548018, 74400047748⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 184156160 184811520 156467200 159252480 ⟨⟨71979107944, 71979107950⟩, ⟨69886174465, 74089819079⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 184811520 185466880 153681920 156467200 ⟨⟨70476610525, 70476610529⟩, ⟨68394803776, 72576112880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 185466880 186122240 153681920 156467200 ⟨⟨70179829269, 70179829275⟩, ⟨68104319405, 72272946541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 184811520 185466880 156467200 159252480 ⟨⟨71676564990, 71676564995⟩, ⟨69589977418, 73780841682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 185466880 186122240 156467200 159252480 ⟨⟨71375225294, 71375225302⟩, ⟨69294946947, 73473104933⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 183500800 186122240 148111360 159252480 t = true :=
  ⟨_, (join_sr (m := 153681920) (by decide) (join_su (m := 184811520) (by decide) (join_sr (m := 150896640) (by decide) (join_su (m := 184156160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 184156160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 150896640) (by decide) (join_su (m := 185466880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 185466880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 184811520) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 184156160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 184156160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 156467200) (by decide) (join_su (m := 185466880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 185466880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/32 : ℝ) (71/320 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e1 : (((186122240 : ℤ) : ℝ) / (D : ℝ)) = (71/320 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

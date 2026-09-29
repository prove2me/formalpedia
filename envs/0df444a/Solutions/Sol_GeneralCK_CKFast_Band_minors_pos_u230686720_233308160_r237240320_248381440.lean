-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_233308160_r237240320_248381440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:37:57.440791+00:00
-- url     : https://prove2.me/submissions/fd1e6935-ec04-4e97-a063-064157e1943c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 89/320]`, `ρ ∈ [181/640, 379/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231342080 237240320 240025600 ⟨⟨78943139457, 78943139461⟩, ⟨77113221658, 80786188274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 231342080 231997440 237240320 240025600 ⟨⟨78599097315, 78599097322⟩, ⟨76773871491, 80437405198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 230686720 231342080 240025600 242810880 ⟨⟨79825635364, 79825635368⟩, ⟨77991896339, 81672512698⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231342080 231997440 240025600 242810880 ⟨⟨79478063239, 79478063246⟩, ⟨77649025295, 81320190680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 231997440 232652800 237240320 240025600 ⟨⟨78255931615, 78255931622⟩, ⟨76435377382, 80089519236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 232652800 233308160 237240320 240025600 ⟨⟨77913636159, 77913636166⟩, ⟨76097733278, 79742524040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231997440 232652800 240025600 242810880 ⟨⟨79131372738, 79131372744⟩, ⟨77307015501, 80968770940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 232652800 233308160 240025600 242810880 ⟨⟨78785557636, 78785557642⟩, ⟨76965860878, 80618247111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 230686720 231342080 242810880 245596160 ⟨⟨80707358044, 80707358048⟩, ⟨78869801006, 82558060618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231342080 231997440 242810880 245596160 ⟨⟨80356265200, 80356265206⟩, ⟨78523418269, 82202208997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 230686720 231342080 245596160 248381440 ⟨⟨81588311359, 81588311361⟩, ⟨79746939502, 83442835911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 231342080 231997440 245596160 248381440 ⟨⟨81233707000, 81233707006⟩, ⟨79397054201, 83083463971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 231997440 232652800 242810880 245596160 ⟨⟨80006059070, 80006059077⟩, ⟨78177901887, 81847264732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 232652800 233308160 242810880 245596160 ⟨⟨79656733409, 79656733415⟩, ⟨77833245756, 81493221432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 231997440 232652800 245596160 248381440 ⟨⟨80879994361, 80879994366⟩, ⟨79048040270, 82725004378⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 232652800 233308160 245596160 248381440 ⟨⟨80527167170, 80527167176⟩, ⟨78699891587, 82367450715⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 233308160 237240320 248381440 t = true :=
  ⟨_, (join_sr (m := 242810880) (by decide) (join_su (m := 231997440) (by decide) (join_sr (m := 240025600) (by decide) (join_su (m := 231342080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 231342080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 240025600) (by decide) (join_su (m := 232652800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 232652800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 231997440) (by decide) (join_sr (m := 245596160) (by decide) (join_su (m := 231342080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 231342080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 245596160) (by decide) (join_su (m := 232652800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 232652800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (89/320 : ℝ) →
    rho ∈ Set.Icc (181/640 : ℝ) (379/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e2 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e3 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

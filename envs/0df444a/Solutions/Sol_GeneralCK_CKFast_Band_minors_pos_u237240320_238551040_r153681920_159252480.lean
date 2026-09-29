-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u237240320_238551040_r153681920_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:03:55.208047+00:00
-- url     : https://prove2.me/submissions/9cef3b7f-49ed-40cb-a86d-78355f478669

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [181/640, 91/320]`, `ρ ∈ [469/2560, 243/1280]` by 13 cells of the computing
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
theorem cell0 : cellOK 237240320 237568000 153681920 155074560 ⟨⟨49622418662, 49622418667⟩, ⟨48785434596, 50462497296⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 237568000 237895680 153681920 155074560 ⟨⟨49509230958, 49509230965⟩, ⟨48673297687, 50348252582⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 237240320 237568000 155074560 156467200 ⟨⟨50057874067, 50057874074⟩, ⟨49219935597, 50898908401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237568000 237895680 155074560 156467200 ⟨⟨49943745034, 49943745039⟩, ⟨49106858794, 50783720925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 237895680 238223360 153681920 155074560 ⟨⟨49396200324, 49396200331⟩, ⟨48561315476, 50234167330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 238223360 238551040 153681920 155074560 ⟨⟨49283326174, 49283326177⟩, ⟨48449487389, 50120240936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237895680 238223360 155074560 156467200 ⟨⟨49829774048, 49829774054⟩, ⟨48993937668, 50668693890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 238223360 238551040 155074560 156467200 ⟨⟨49715960520, 49715960523⟩, ⟨48881171639, 50553826692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 237240320 237895680 156467200 157859840 ⟨⟨50435576039, 50435576042⟩, ⟨49008833906, 51870974266⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 237240320 237895680 157859840 159252480 ⟨⟨50870164451, 50870164454⟩, ⟨49441664765, 52307325851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 237895680 238223360 156467200 157859840 ⟨⟨50263151329, 50263151336⟩, ⟨49426363779, 51103023647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 238223360 238551040 156467200 157859840 ⟨⟨50148399680, 50148399683⟩, ⟨49312661058, 50987216904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 237895680 238551040 157859840 159252480 ⟨⟨50638468489, 50638468494⟩, ⟨49212924195, 52072645425⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 237240320 238551040 153681920 159252480 t = true :=
  ⟨_, (join_sr (m := 156467200) (by decide) (join_su (m := 237895680) (by decide) (join_sr (m := 155074560) (by decide) (join_su (m := 237568000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 237568000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 155074560) (by decide) (join_su (m := 238223360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 238223360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 237895680) (by decide) (join_sr (m := 157859840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 157859840) (by decide) (join_su (m := 238223360) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (181/640 : ℝ) (91/320 : ℝ) →
    rho ∈ Set.Icc (469/2560 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e1 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e2 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

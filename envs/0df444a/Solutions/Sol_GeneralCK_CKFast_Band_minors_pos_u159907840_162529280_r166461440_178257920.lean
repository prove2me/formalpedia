-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u159907840_162529280_r166461440_178257920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:46:47.196513+00:00
-- url     : https://prove2.me/submissions/e1f8fd2b-24f3-451e-a121-e77f17fb785c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [61/320, 31/160]`, `ρ ∈ [127/640, 17/80]` by 12 cells of the computing
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
theorem cell0 : cellOK 159907840 160563200 166461440 169410560 ⟨⟨89101744081, 89101744089⟩, ⟨86674179944, 91551804702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 160563200 161218560 166461440 169410560 ⟨⟨88728218832, 88728218840⟩, ⟨86308929297, 91169879681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 159907840 160563200 169410560 172359680 ⟨⟨90551355285, 90551355293⟩, ⟨88118315155, 93006861060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 160563200 161218560 169410560 172359680 ⟨⟨90172593185, 90172593194⟩, ⟨87747837589, 92619690024⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 161218560 161873920 166461440 169410560 ⟨⟨88356419900, 88356419908⟩, ⟨85945351110, 90789735932⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 161873920 162529280 166461440 169410560 ⟨⟨87986331478, 87986331480⟩, ⟨85583430124, 90411357087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 161218560 161873920 169410560 172359680 ⟨⟨89795572543, 89795572550⟩, ⟨87379047725, 92234315288⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 161873920 162529280 169410560 172359680 ⟨⟨89420277467, 89420277471⟩, ⟨87011930218, 91850720401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 159907840 161218560 172359680 175308800 ⟨⟨91805395705, 91805395710⟩, ⟨87884900886, 95783606473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 159907840 161218560 175308800 178257920 ⟨⟨93245711315, 93245711320⟩, ⟨89315482698, 97233610273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 161218560 162529280 172359680 175308800 ⟨⟨91040978363, 91040978369⟩, ⟨87144151029, 94994951724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 161218560 162529280 175308800 178257920 ⟨⟨92470992474, 92470992481⟩, ⟨88564464556, 96434624190⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 159907840 162529280 166461440 178257920 t = true :=
  ⟨_, (join_sr (m := 172359680) (by decide) (join_su (m := 161218560) (by decide) (join_sr (m := 169410560) (by decide) (join_su (m := 160563200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 160563200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 169410560) (by decide) (join_su (m := 161873920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 161873920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 161218560) (by decide) (join_sr (m := 175308800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 175308800) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (61/320 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (127/640 : ℝ) (17/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  have e3 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

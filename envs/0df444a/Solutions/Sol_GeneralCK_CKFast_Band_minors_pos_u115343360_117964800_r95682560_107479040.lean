-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_117964800_r95682560_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:12:50.938143+00:00
-- url     : https://prove2.me/submissions/023af984-8ede-410a-8d8f-3f06bb8f3718

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 9/64]`, `ρ ∈ [73/640, 41/320]` by 20 cells of the computing
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
theorem cell0 : cellOK 115343360 115998720 95682560 97157120 ⟨⟨72544334393, 72544334402⟩, ⟨70196243254, 74915511332⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 115343360 115998720 97157120 98631680 ⟨⟨73565664176, 73565664184⟩, ⟨71214221486, 75940160867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 115998720 116654080 95682560 97157120 ⟨⟨72184846524, 72184846530⟩, ⟨69846757174, 74545842827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 115998720 116654080 97157120 98631680 ⟨⟨73201828063, 73201828065⟩, ⟨70860395006, 75566137037⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 115343360 115998720 98631680 101580800 ⟨⟨75093349934, 75093349942⟩, ⟨72088703367, 78135592655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 115998720 116654080 98631680 101580800 ⟨⟨74723043690, 74723043696⟩, ⟨71732145421, 77751229897⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 116654080 117309440 95682560 97157120 ⟨⟨71828037605, 71828037612⟩, ⟨69499853263, 74178952379⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 116654080 117309440 97157120 98631680 ⟨⟨72840694682, 72840694689⟩, ⟨70509174566, 75194914946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 117309440 117964800 95682560 97157120 ⟨⟨71473872800, 71473872808⟩, ⟨69155498103, 73814803688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 117309440 117964800 97157120 98631680 ⟨⟨72482228984, 72482228992⟩, ⟨70160526524, 74826458082⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 116654080 117309440 98631680 101580800 ⟨⟨74355475157, 74355475166⟩, ⟨71378195582, 77369738452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 117309440 117964800 98631680 101580800 ⟨⟨73990608971, 73990608979⟩, ⟨71026820365, 76991080994⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 115343360 115998720 101580800 104529920 ⟨⟨77122292049, 77122292058⟩, ⟨74110091643, 80171956478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 115998720 116654080 101580800 104529920 ⟨⟨76743455200, 76743455205⟩, ⟨73745018499, 79779050531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 115343360 115998720 104529920 107479040 ⟨⟨79142221059, 79142221067⟩, ⟨76122566675, 82199207303⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 115998720 116654080 104529920 107479040 ⟨⟨78754961836, 78754961842⟩, ⟨75749085093, 81797867858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 116654080 117309440 101580800 104529920 ⟨⟨76367401418, 76367401425⟩, ⟨73382599115, 79389060896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 117309440 117964800 101580800 104529920 ⟨⟨75994094936, 75994094945⟩, ⟨73022799595, 79001949860⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 116654080 117309440 104529920 107479040 ⟨⟨78370529604, 78370529612⟩, ⟨75378301513, 81399488272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 117309440 117964800 104529920 107479040 ⟨⟨77988888222, 77988888231⟩, ⟨75010181653, 81004030471⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 117964800 95682560 107479040 t = true :=
  ⟨_, (join_sr (m := 101580800) (by decide) (join_su (m := 116654080) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 115998720) (by decide) (join_sr (m := 97157120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 97157120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 115998720) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 98631680) (by decide) (join_su (m := 117309440) (by decide) (join_sr (m := 97157120) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 97157120) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 117309440) (by decide) (leaf_ok cell10) (leaf_ok cell11)))) (join_su (m := 116654080) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 115998720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 115998720) (by decide) (leaf_ok cell14) (leaf_ok cell15))) (join_sr (m := 104529920) (by decide) (join_su (m := 117309440) (by decide) (leaf_ok cell16) (leaf_ok cell17)) (join_su (m := 117309440) (by decide) (leaf_ok cell18) (leaf_ok cell19)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (9/64 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((117964800 : ℤ) : ℝ) / (D : ℝ)) = (9/64 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

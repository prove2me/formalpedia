-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_180879360_r170393600_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:37:44.842956+00:00
-- url     : https://prove2.me/submissions/32975cc5-9b43-404d-8ef3-42b447e78a1a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 69/320]`, `ρ ∈ [13/64, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 178913280 170393600 173178880 ⟨⟨80955128077, 80955128080⟩, ⟨78779107483, 83149701424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178913280 179568640 170393600 173178880 ⟨⟨80618208892, 80618208899⟩, ⟨78448937226, 82805940249⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 178257920 178913280 173178880 175964160 ⟨⟨82187883042, 82187883045⟩, ⟨80007058577, 84387248876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 178913280 179568640 173178880 175964160 ⟨⟨81846423032, 81846423039⟩, ⟨79672358167, 84038936643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 179568640 180224000 170393600 173178880 ⟨⟨80282652902, 80282652909⟩, ⟨78120090420, 82463582754⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 180224000 180879360 170393600 173178880 ⟨⟨79948448533, 79948448539⟩, ⟨77792555859, 82122616989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 179568640 180224000 173178880 175964160 ⟨⟨81506338151, 81506338158⟩, ⟨79338993182, 83692039977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 180224000 180879360 173178880 175964160 ⟨⟨81167616758, 81167616765⟩, ⟨79006952350, 83346546864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 178257920 178913280 175964160 178749440 ⟨⟨83418440263, 83418440265⟩, ⟨81232828029, 85622582347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 178913280 179568640 175964160 178749440 ⟨⟨83072463373, 83072463379⟩, ⟨80893621172, 85269743241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 178257920 178913280 178749440 181534720 ⟨⟨84646814195, 84646814198⟩, ⟨82456430157, 86855716427⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 178913280 179568640 178749440 181534720 ⟨⟨84296344156, 84296344162⟩, ⟨82112740347, 86498374416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 179568640 180224000 175964160 178749440 ⟨⟨82727873308, 82727873314⟩, ⟨80555761478, 84918331349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 180224000 180879360 175964160 178749440 ⟨⟨82384658363, 82384658369⟩, ⟨80219237613, 84568334592⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 179568640 180224000 178749440 181534720 ⟨⟨83947272402, 83947272408⟩, ⟨81770409209, 86142471023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 180224000 180879360 178749440 181534720 ⟨⟨83599587169, 83599587176⟩, ⟨81429425343, 85787994119⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 180879360 170393600 181534720 t = true :=
  ⟨_, (join_sr (m := 175964160) (by decide) (join_su (m := 179568640) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 178913280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 178913280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 173178880) (by decide) (join_su (m := 180224000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 180224000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 179568640) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 178913280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 178913280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178749440) (by decide) (join_su (m := 180224000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 180224000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (69/320 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((180879360 : ℤ) : ℝ) / (D : ℝ)) = (69/320 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

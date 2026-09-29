-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_214958080_r304087040_315228160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:00:40.065928+00:00
-- url     : https://prove2.me/submissions/0f1bcae2-71a2-42af-a821-6b1957b82669

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 41/160]`, `ρ ∈ [29/80, 481/1280]` by 14 cells of the computing
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
theorem cell0 : cellOK 209715200 211025920 304087040 306872320 ⟨⟨113887003436, 113887003444⟩, ⟨110366904824, 117448581262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 209715200 211025920 306872320 309657600 ⟨⟨114858360512, 114858360520⟩, ⟨111330918634, 118427297402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 211025920 212336640 304087040 306872320 ⟨⟨112966638333, 112966638339⟩, ⟨109462628417, 116511874876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 211025920 212336640 306872320 309657600 ⟨⟨113931139923, 113931139931⟩, ⟨110419807643, 117483715831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 209715200 211025920 309657600 315228160 ⟨⟨116313568383, 116313568390⟩, ⟨112136999581, 120549517744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 211025920 212336640 309657600 315228160 ⟨⟨115376103779, 115376103787⟩, ⟨111221800642, 119589363627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212336640 213647360 304087040 306872320 ⟨⟨112051090529, 112051090532⟩, ⟨108563021543, 115580136406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 212336640 213647360 306872320 309657600 ⟨⟨113008750553, 113008750557⟩, ⟨109513380435, 116545115737⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 213647360 214958080 304087040 306872320 ⟨⟨111140293901, 111140293909⟩, ⟨107668020165, 114653297610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 213647360 214958080 306872320 309657600 ⟨⟨112091126238, 112091126245⟩, ⟨108611572916, 115611428849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 212336640 213647360 309657600 312442880 ⟨⟨113965476395, 113965476398⟩, ⟨110462812291, 117509153464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 212336640 213647360 312442880 315228160 ⟨⟨114921273210, 114921273213⟩, ⟨111411322224, 118472254784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 213647360 214958080 309657600 312442880 ⟨⟨113041044622, 113041044630⟩, ⟨109554218576, 116568639005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 213647360 214958080 312442880 315228160 ⟨⟨113990054070, 113990054078⟩, ⟨110495962121, 117524933138⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 214958080 304087040 315228160 t = true :=
  ⟨_, (join_su (m := 212336640) (by decide) (join_sr (m := 309657600) (by decide) (join_su (m := 211025920) (by decide) (join_sr (m := 306872320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 306872320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 211025920) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 309657600) (by decide) (join_su (m := 213647360) (by decide) (join_sr (m := 306872320) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 306872320) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 213647360) (by decide) (join_sr (m := 312442880) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 312442880) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (29/80 : ℝ) (481/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  have e3 : (((315228160 : ℤ) : ℝ) / (D : ℝ)) = (481/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

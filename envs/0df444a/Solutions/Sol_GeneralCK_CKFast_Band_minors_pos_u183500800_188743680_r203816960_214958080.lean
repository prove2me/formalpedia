-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u183500800_188743680_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:18:24.901499+00:00
-- url     : https://prove2.me/submissions/6cd27099-75e9-41a8-af36-bebae81f9aab

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/32, 9/40]`, `ρ ∈ [311/1280, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 183500800 184811520 203816960 206602240 ⟨⟨92339034956, 92339034963⟩, ⟨88749682266, 95975903641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 183500800 184811520 206602240 209387520 ⟨⟨93510370209, 93510370216⟩, ⟨89912728909, 97155525798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 184811520 186122240 203816960 206602240 ⟨⟨91585269104, 91585269110⟩, ⟨88014734348, 95202931382⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 184811520 186122240 206602240 209387520 ⟨⟨92748234217, 92748234225⟩, ⟨89169440458, 96374155608⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 183500800 184811520 209387520 212172800 ⟨⟨94679850886, 94679850892⟩, ⟨91073940362, 98333273578⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 183500800 184811520 212172800 214958080 ⟨⟨95847488700, 95847488708⟩, ⟨92233328198, 99509158840⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 184811520 186122240 209387520 212172800 ⟨⟨93909384262, 93909384270⟩, ⟨90322350291, 97543545566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 184811520 186122240 212172800 214958080 ⟨⟨95068730621, 95068730628⟩, ⟨91473475091, 98711112775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 186122240 187432960 203816960 206602240 ⟨⟨90837024694, 90837024695⟩, ⟨87285091826, 94435702347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 186122240 187432960 206602240 209387520 ⟨⟨91991655294, 91991655298⟩, ⟨88431493330, 95598563919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 187432960 188743680 203816960 206602240 ⟨⟨90094213552, 90094213558⟩, ⟨86560670268, 93674124523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 187432960 188743680 206602240 209387520 ⟨⟨91240544955, 91240544961⟩, ⟨87698802760, 94828658419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 186122240 187432960 209387520 212172800 ⟨⟨93144509597, 93144509600⟩, ⟨89576136740, 96759630580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 186122240 187432960 212172800 214958080 ⟨⟨94295598654, 94295598658⟩, ⟨90719032983, 97918913518⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 187432960 188743680 209387520 212172800 ⟨⟨92385138099, 92385138105⟩, ⟨88835214628, 95981436023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 187432960 188743680 212172800 214958080 ⟨⟨93528003724, 93528003731⟩, ⟨89969916488, 97132468202⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 183500800 188743680 203816960 214958080 t = true :=
  ⟨_, (join_su (m := 186122240) (by decide) (join_sr (m := 209387520) (by decide) (join_su (m := 184811520) (by decide) (join_sr (m := 206602240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 206602240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 184811520) (by decide) (join_sr (m := 212172800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 212172800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 209387520) (by decide) (join_su (m := 187432960) (by decide) (join_sr (m := 206602240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 206602240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 187432960) (by decide) (join_sr (m := 212172800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 212172800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/32 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

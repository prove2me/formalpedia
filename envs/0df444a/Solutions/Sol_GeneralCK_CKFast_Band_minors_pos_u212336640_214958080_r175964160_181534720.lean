-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u212336640_214958080_r175964160_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:20:17.68941+00:00
-- url     : https://prove2.me/submissions/6e3caff3-1c3f-47eb-bc58-402c3d597959

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [81/320, 41/160]`, `ρ ∈ [537/2560, 277/1280]` by 8 cells of the computing
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
theorem cell0 : cellOK 212336640 212992000 175964160 178749440 ⟨⟨67037849117, 67037849123⟩, ⟨65158722724, 68931532564⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 212992000 213647360 175964160 178749440 ⟨⟨66750830914, 66750830919⟩, ⟨64876814450, 68639341793⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212336640 212992000 178749440 181534720 ⟨⟨68046497603, 68046497608⟩, ⟨66163164376, 69944392102⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212992000 213647360 178749440 181534720 ⟨⟨67755506838, 67755506845⟩, ⟨65877294685, 69648217825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 213647360 214302720 175964160 178749440 ⟨⟨66464725144, 66464725150⟩, ⟨64595793285, 68348089214⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 214302720 214958080 175964160 178749440 ⟨⟨66179524824, 66179524826⟩, ⟨64315652443, 68057767636⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 213647360 214302720 178749440 181534720 ⟨⟨67465437120, 67465437128⟩, ⟨65592320714, 69352990351⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 214302720 214958080 178749440 181534720 ⟨⟨67176281415, 67176281420⟩, ⟨65308235629, 69058702438⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 212336640 214958080 175964160 181534720 t = true :=
  ⟨_, (join_su (m := 213647360) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 212992000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 212992000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 178749440) (by decide) (join_su (m := 214302720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 214302720) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (81/320 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (537/2560 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((175964160 : ℤ) : ℝ) / (D : ℝ)) = (537/2560 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

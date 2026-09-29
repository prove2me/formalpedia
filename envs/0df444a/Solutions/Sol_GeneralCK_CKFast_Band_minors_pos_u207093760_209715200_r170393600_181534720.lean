-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u207093760_209715200_r170393600_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:16:40.393973+00:00
-- url     : https://prove2.me/submissions/43b00af6-d4ed-411a-b69f-c24966b8fab4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [79/320, 1/4]`, `ρ ∈ [13/64, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 207093760 207749120 170393600 173178880 ⟨⟨67282206442, 67282206448⟩, ⟨65369879224, 69209602515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 207749120 208404480 170393600 173178880 ⟨⟨66995761992, 66995761995⟩, ⟨65088732161, 68917793984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 207093760 207749120 173178880 175964160 ⟨⟨68325624526, 68325624531⟩, ⟨66408985705, 70257334921⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 207749120 208404480 173178880 175964160 ⟨⟨68035106046, 68035106049⟩, ⟨66123776035, 69961441162⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 208404480 209059840 170393600 173178880 ⟨⟨66710269766, 66710269772⟩, ⟨64808510302, 68626965180⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209059840 209715200 170393600 173178880 ⟨⟨66425722352, 66425722359⟩, ⟨64529206450, 68337108459⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 208404480 209059840 173178880 175964160 ⟨⟨67745549106, 67745549112⟩, ⟨65839500881, 69666536441⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 209059840 209715200 173178880 175964160 ⟨⟨67456946238, 67456946245⟩, ⟨65556152993, 69372613063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 207093760 207749120 175964160 178749440 ⟨⟨69367702293, 69367702299⟩, ⟨67446759709, 71303719076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 207749120 208404480 175964160 178749440 ⟨⟨69073125239, 69073125241⟩, ⟨67157502742, 71003755687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 207093760 207749120 178749440 181534720 ⟨⟨70408447202, 70408447209⟩, ⟨68483208640, 72348762489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 207749120 208404480 178749440 181534720 ⟨⟨70109826915, 70109826918⟩, ⟨68189919578, 72044744952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 208404480 209059840 175964160 178749440 ⟨⟨68779518884, 68779518890⟩, ⟨66869189453, 70704790491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 209059840 209715200 175964160 178749440 ⟨⟨68486875711, 68486875717⟩, ⟨66581812539, 70406815742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 208404480 209059840 178749440 181534720 ⟨⟨69812186335, 69812186342⟩, ⟨67897583203, 71741734612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 209059840 209715200 178749440 181534720 ⟨⟨69515517897, 69515517903⟩, ⟨67606192167, 71439723672⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 207093760 209715200 170393600 181534720 t = true :=
  ⟨_, (join_sr (m := 175964160) (by decide) (join_su (m := 208404480) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 207749120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 207749120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 173178880) (by decide) (join_su (m := 209059840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 209059840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 208404480) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 207749120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 207749120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178749440) (by decide) (join_su (m := 209059840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 209059840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (79/320 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((207093760 : ℤ) : ℝ) / (D : ℝ)) = (79/320 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

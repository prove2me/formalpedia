-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u186122240_188743680_r170393600_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:37:54.153996+00:00
-- url     : https://prove2.me/submissions/0b2d890a-7e3e-41d8-b257-70a4069b6786

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [71/320, 9/40]`, `ρ ∈ [13/64, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 186122240 186777600 170393600 173178880 ⟨⟨76999582925, 76999582931⟩, ⟨74902005398, 79114643876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 186777600 187432960 170393600 173178880 ⟨⟨76678284827, 76678284834⟩, ⟨74587002694, 78786965752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 186122240 186777600 173178880 175964160 ⟨⟨78178621327, 78178621333⟩, ⟨76076370358, 80298349185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 186777600 187432960 173178880 175964160 ⟨⟨77852921344, 77852921352⟩, ⟨75756976839, 79966258471⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 187432960 188088320 170393600 173178880 ⟨⟨76358218904, 76358218912⟩, ⟨74273196566, 78460556059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 188088320 188743680 170393600 173178880 ⟨⟨76039374974, 76039374977⟩, ⟨73960577142, 78135404286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 187432960 188088320 173178880 175964160 ⟨⟨77528464704, 77528464712⟩, ⟨75438791085, 79635447325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 188088320 188743680 173178880 175964160 ⟨⟨77205241159, 77205241162⟩, ⟨75121803164, 79305905173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 186122240 186777600 175964160 178749440 ⟨⟨79355734159, 79355734165⟩, ⟨77248823161, 81480115382⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 186777600 187432960 175964160 178749440 ⟨⟨79025653540, 79025653547⟩, ⟨76925059864, 81143633536⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 186122240 186777600 178749440 181534720 ⟨⟨80530933500, 80530933506⟩, ⟨78419375777, 82659954655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 186777600 187432960 178749440 181534720 ⟨⟨80196493311, 80196493317⟩, ⟨78091263566, 82319102951⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 187432960 188088320 175964160 178749440 ⟨⟨78696827219, 78696827225⟩, ⟨76602515316, 80808442182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 188088320 188743680 175964160 178749440 ⟨⟨78369244887, 78369244888⟩, ⟨76281179524, 80474530683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 187432960 188088320 178749440 181534720 ⟨⟨79863318167, 79863318175⟩, ⟨77764380882, 81979552450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 188088320 188743680 178749440 181534720 ⟨⟨79531397704, 79531397707⟩, ⟨77438717672, 81641292463⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 186122240 188743680 170393600 181534720 t = true :=
  ⟨_, (join_sr (m := 175964160) (by decide) (join_su (m := 187432960) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 186777600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 186777600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 173178880) (by decide) (join_su (m := 188088320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 188088320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 187432960) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 186777600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 186777600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178749440) (by decide) (join_su (m := 188088320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 188088320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (71/320 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((186122240 : ℤ) : ℝ) / (D : ℝ)) = (71/320 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

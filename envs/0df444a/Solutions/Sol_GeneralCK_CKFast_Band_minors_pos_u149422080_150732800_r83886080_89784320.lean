-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u149422080_150732800_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:59:56.201887+00:00
-- url     : https://prove2.me/submissions/6898817b-f6df-47d5-b56c-aa276d45b131

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [57/320, 23/128]`, `ρ ∈ [1/10, 137/1280]` by 11 cells of the computing
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
theorem cell0 : cellOK 149422080 149749760 83886080 85360640 ⟨⟨50201050435, 50201050441⟩, ⟨49000335003, 51408240079⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 149749760 150077440 83886080 85360640 ⟨⟨50086489343, 50086489346⟩, ⟨48887985016, 51291446099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 149422080 150077440 85360640 86835200 ⟨⟨50976354484, 50976354492⟩, ⟨49065803977, 52903107547⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 150077440 150405120 83886080 85360640 ⟨⟨49972262104, 49972262112⟩, ⟨48775960575, 51174994405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 150405120 150732800 83886080 85360640 ⟨⟨49858366918, 49858366924⟩, ⟨48664259930, 51058883131⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 150077440 150405120 85360640 86835200 ⟨⟨50802281506, 50802281513⟩, ⟨49604285006, 52006703992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 150405120 150732800 85360640 86835200 ⟨⟨50686653451, 50686653457⟩, ⟨49490854581, 51888856824⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 149422080 150077440 86835200 88309760 ⟨⟨51807697121, 51807697128⟩, ⟨49894191141, 53737398872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 149422080 150077440 88309760 89784320 ⟨⟨52637761708, 52637761716⟩, ⟨50721309411, 54570402934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 150077440 150732800 86835200 88309760 ⟨⟨51572309387, 51572309395⟩, ⟨49665127037, 53495588498⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 150077440 150732800 88309760 89784320 ⟨⟨52398930229, 52398930237⟩, ⟨50488811401, 54325139239⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 149422080 150732800 83886080 89784320 t = true :=
  ⟨_, (join_sr (m := 86835200) (by decide) (join_su (m := 150077440) (by decide) (join_sr (m := 85360640) (by decide) (join_su (m := 149749760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 85360640) (by decide) (join_su (m := 150405120) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (join_su (m := 150405120) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_su (m := 150077440) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 88309760) (by decide) (leaf_ok cell9) (leaf_ok cell10))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (57/320 : ℝ) (23/128 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((149422080 : ℤ) : ℝ) / (D : ℝ)) = (57/320 : ℝ) := by norm_num [D]
  have e1 : (((150732800 : ℤ) : ℝ) / (D : ℝ)) = (23/128 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

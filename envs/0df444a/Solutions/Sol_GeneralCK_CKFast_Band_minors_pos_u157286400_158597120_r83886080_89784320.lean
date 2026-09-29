-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_158597120_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:10:33.877514+00:00
-- url     : https://prove2.me/submissions/d4f6dc2f-8fca-4bf8-b6f2-ccf5b4538767

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 121/640]`, `ρ ∈ [1/10, 137/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 157614080 83886080 85360640 ⟨⟨47540202444, 47540202452⟩, ⟨46390356446, 48696030484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157614080 157941760 83886080 85360640 ⟨⟨47433179970, 47433179976⟩, ⟨46285358554, 48586964225⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157286400 157614080 85360640 86835200 ⟨⟨48333019633, 48333019639⟩, ⟨47181545673, 49490472098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 157614080 157941760 85360640 86835200 ⟨⟨48224350533, 48224350539⟩, ⟨47074904151, 49379756269⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 157941760 158269440 83886080 85360640 ⟨⟨47326451316, 47326451319⟩, ⟨46180647259, 48478199103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 158269440 158597120 83886080 85360640 ⟨⟨47220014949, 47220014957⟩, ⟨46076221070, 48369733558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 157941760 158269440 85360640 86835200 ⟨⟨48115978979, 48115978982⟩, ⟨46968552947, 49269345307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 158269440 158597120 85360640 86835200 ⟨⟨48007903422, 48007903428⟩, ⟨46862490553, 49159237632⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 157286400 157614080 86835200 88309760 ⟨⟨49124720067, 49124720075⟩, ⟨47971623284, 50283791806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 157614080 157941760 86835200 88309760 ⟨⟨49014410936, 49014410942⟩, ⟨47863344687, 50171433040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 157286400 157614080 88309760 89784320 ⟨⟨49915308465, 49915308471⟩, ⟨48760593967, 51075994351⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 157614080 157941760 88309760 89784320 ⟨⟨49803365854, 49803365862⟩, ⟨48650684807, 50961999241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 157941760 158269440 86835200 88309760 ⟨⟨48904403035, 48904403038⟩, ⟨47755360088, 50059382830⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 158269440 158597120 86835200 88309760 ⟨⟨48794694800, 48794694808⟩, ⟨47647667965, 49947639581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 157941760 158269440 88309760 89784320 ⟨⟨49691728121, 49691728124⟩, ⟨48541073288, 50848316337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 158269440 158597120 88309760 89784320 ⟨⟨49580393686, 49580393692⟩, ⟨48431757871, 50734944030⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 158597120 83886080 89784320 t = true :=
  ⟨_, (join_sr (m := 86835200) (by decide) (join_su (m := 157941760) (by decide) (join_sr (m := 85360640) (by decide) (join_su (m := 157614080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 157614080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 85360640) (by decide) (join_su (m := 158269440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 158269440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 157941760) (by decide) (join_sr (m := 88309760) (by decide) (join_su (m := 157614080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 157614080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 88309760) (by decide) (join_su (m := 158269440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 158269440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (121/640 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((158597120 : ℤ) : ℝ) / (D : ℝ)) = (121/640 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u186122240_188743680_r159252480_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:37:14.849469+00:00
-- url     : https://prove2.me/submissions/05e6389f-c4a0-4a35-bd52-17fcbac16e52

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [71/320, 9/40]`, `ρ ∈ [243/1280, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 186122240 186777600 159252480 162037760 ⟨⟨72263929091, 72263929099⟩, ⟨70185181539, 74360184919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 186777600 187432960 159252480 162037760 ⟨⟨71960454660, 71960454668⟩, ⟨69887956107, 74050375407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 186122240 186777600 162037760 164823040 ⟨⟨73450792249, 73450792255⟩, ⟨71367316559, 75551770196⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 186777600 187432960 162037760 164823040 ⟨⟨73142829113, 73142829119⟩, ⟨71065614342, 75237460418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 187432960 188088320 159252480 162037760 ⟨⟨71658165583, 71658165591⟩, ⟨69591880353, 73741787604⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 188088320 188743680 159252480 162037760 ⟨⟨71357051948, 71357051951⟩, ⟨69296944684, 73434411264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 187432960 188088320 162037760 164823040 ⟨⟨72836063364, 72836063370⟩, ⟨70765073854, 74924384361⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 188088320 188743680 162037760 164823040 ⟨⟨72530485019, 72530485021⟩, ⟨70465685427, 74612531713⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 186122240 186777600 164823040 167608320 ⟨⟨74635680675, 74635680681⟩, ⟨72547490681, 76741366780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 186777600 187432960 164823040 167608320 ⟨⟨74323250817, 74323250823⟩, ⟨72241333448, 76422578935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 186122240 186777600 167608320 170393600 ⟨⟨75818606790, 75818606797⟩, ⟨73725716219, 77928987193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 186777600 187432960 167608320 170393600 ⟨⟨75501732005, 75501732013⟩, ⟨73415125551, 77605743295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 187432960 188088320 164823040 167608320 ⟨⟨74012030158, 74012030166⟩, ⟨71936349772, 76105036603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 188088320 188743680 164823040 167608320 ⟨⟨73702008649, 73702008652⟩, ⟨71632529920, 75788729401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 187432960 188088320 167608320 170393600 ⟨⟨75186078018, 75186078025⟩, ⟨73105720055, 77283756480⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 188088320 188743680 167608320 170393600 ⟨⟨74871634706, 74871634709⟩, ⟨72797489930, 76963016297⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 186122240 188743680 159252480 170393600 t = true :=
  ⟨_, (join_sr (m := 164823040) (by decide) (join_su (m := 187432960) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 186777600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 186777600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 162037760) (by decide) (join_su (m := 188088320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 188088320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 187432960) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 186777600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 186777600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 167608320) (by decide) (join_su (m := 188088320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 188088320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (71/320 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((186122240 : ℤ) : ℝ) / (D : ℝ)) = (71/320 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

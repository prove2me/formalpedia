-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u52428800_54525952_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:57:28.983106+00:00
-- url     : https://prove2.me/submissions/74b2c8cd-5ee8-4492-bba8-93debe9c2a25

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/16, 13/200]`, `ρ ∈ [3/40, 229/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 52428800 52953088 62914560 65945600 ⟨⟨92297265471, 92297265483⟩, ⟨87355924638, 97342783299⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 52953088 53477376 62914560 65945600 ⟨⟨91677242489, 91677242504⟩, ⟨86773553616, 96683655258⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 52428800 52953088 65945600 68976640 ⟨⟨95986348978, 95986348993⟩, ⟨91037855257, 101037659705⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 52953088 53477376 65945600 68976640 ⟨⟨95347878795, 95347878807⟩, ⟨90436892220, 100360263851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 53477376 54001664 62914560 65945600 ⟨⟨91065388347, 91065388358⟩, ⟨86198750259, 96033328648⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 54001664 54525952 62914560 65945600 ⟨⟨90461530433, 90461530448⟩, ⟨85631356470, 95391615445⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 53477376 54001664 65945600 68976640 ⟨⟨94717725092, 94717725106⟩, ⟨89843651524, 99691808959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 54001664 54525952 65945600 68976640 ⟨⟨94095713965, 94095713977⟩, ⟨89257973462, 99032106042⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 52428800 52953088 68976640 72007680 ⟨⟨99629304219, 99629304234⟩, ⟨94674347914, 104685737297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 52953088 53477376 68976640 72007680 ⟨⟨98973040940, 98973040952⟩, ⟨94055436445, 103990737449⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 52428800 52953088 72007680 75038720 ⟨⟨103227373028, 103227373040⟩, ⟨98266608627, 108288293608⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 52953088 53477376 72007680 75038720 ⟨⟨102553943194, 102553943207⟩, ⟨97630365669, 107576325105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 53477376 54001664 68976640 72007680 ⟨⟨98325229900, 98325229915⟩, ⟨93444390242, 103304806103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 54001664 54525952 68976640 72007680 ⟨⟨97685696159, 97685696171⟩, ⟨92841048281, 102627753561⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 53477376 54001664 72007680 75038720 ⟨⟨101889090213, 101889090225⟩, ⟨97002119879, 106873541403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 54001664 54525952 72007680 75038720 ⟨⟨101232638344, 101232638359⟩, ⟨96381709151, 106179752343⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 52428800 54525952 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 53477376) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 52953088) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 52953088) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 65945600) (by decide) (join_su (m := 54001664) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 54001664) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 53477376) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 52953088) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 52953088) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 72007680) (by decide) (join_su (m := 54001664) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 54001664) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/16 : ℝ) (13/200 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((52428800 : ℤ) : ℝ) / (D : ℝ)) = (1/16 : ℝ) := by norm_num [D]
  have e1 : (((54525952 : ℤ) : ℝ) / (D : ℝ)) = (13/200 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

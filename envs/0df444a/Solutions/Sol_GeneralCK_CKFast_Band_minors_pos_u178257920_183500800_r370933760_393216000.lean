-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_183500800_r370933760_393216000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:04:28.838441+00:00
-- url     : https://prove2.me/submissions/aa90f368-3ff8-4b81-ae90-a5cf21698808

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 7/32]`, `ρ ∈ [283/640, 15/32]` by 14 cells of the computing
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
theorem cell0 : cellOK 178257920 179568640 370933760 376504320 ⟨⟨165107553819, 165107553828⟩, ⟨160152848496, 170131797458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 179568640 180879360 370933760 376504320 ⟨⟨163880782320, 163880782324⟩, ⟨158953997625, 168876625038⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 178257920 179568640 376504320 382074880 ⟨⟨167313730157, 167313730165⟩, ⟨162343327106, 172353516071⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 179568640 180879360 376504320 382074880 ⟨⟨166073981955, 166073981958⟩, ⟨161131492923, 171085380715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 180879360 182190080 370933760 376504320 ⟨⟨162661003132, 162661003141⟩, ⟨157761885287, 167628703558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 182190080 183500800 370933760 376504320 ⟨⟨161448120021, 161448120028⟩, ⟨156576418854, 166387933091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 180879360 182190080 376504320 382074880 ⟨⟨164841232246, 164841232255⟩, ⟨159926405642, 169824500126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 182190080 183500800 376504320 382074880 ⟨⟨163615385185, 163615385192⟩, ⟨158727972975, 168570774828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 178257920 180879360 382074880 387645440 ⟨⟨168887291893, 168887291902⟩, ⟨160614446729, 177350331133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 178257920 180879360 387645440 393216000 ⟨⟨171076307673, 171076307682⟩, ⟨162774295260, 179568244846⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 180879360 182190080 382074880 387645440 ⟨⟨167016239820, 167016239829⟩, ⟨162085771501, 172015006569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 182190080 183500800 382074880 387645440 ⟨⟨165777526361, 165777526368⟩, ⟨160874468533, 170748425609⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 180879360 182190080 387645440 393216000 ⟨⟨169186092972, 169186092980⟩, ⟨164240048934, 174200291058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 182190080 183500800 387645440 393216000 ⟨⟨167934609049, 167934609057⟩, ⟨163015970017, 172920951949⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 183500800 370933760 393216000 t = true :=
  ⟨_, (join_sr (m := 382074880) (by decide) (join_su (m := 180879360) (by decide) (join_sr (m := 376504320) (by decide) (join_su (m := 179568640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 179568640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 376504320) (by decide) (join_su (m := 182190080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 182190080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 180879360) (by decide) (join_sr (m := 387645440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 387645440) (by decide) (join_su (m := 182190080) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_su (m := 182190080) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (283/640 : ℝ) (15/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  have e3 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

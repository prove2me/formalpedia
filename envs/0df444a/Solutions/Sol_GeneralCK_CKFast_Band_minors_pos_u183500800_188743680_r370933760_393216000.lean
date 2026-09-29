-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u183500800_188743680_r370933760_393216000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:03:46.49114+00:00
-- url     : https://prove2.me/submissions/3df4464f-90ab-428e-9f6e-bfb0122aefdf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/32, 9/40]`, `ρ ∈ [283/640, 15/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 183500800 184811520 370933760 376504320 ⟨⟨160242038350, 160242038357⟩, ⟨155397507254, 165154215382⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 184811520 186122240 370933760 376504320 ⟨⟨159042665066, 159042665075⟩, ⟨154225060930, 163927453828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 183500800 184811520 376504320 382074880 ⟨⟨162396346511, 162396346519⟩, ⟨157536104167, 167324107005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 184811520 186122240 376504320 382074880 ⟨⟨161184023536, 161184023544⟩, ⟨156350709961, 166084400474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 186122240 187432960 370933760 376504320 ⟨⟨157849908664, 157849908668⟩, ⟨153058991794, 162707553434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 187432960 188743680 370933760 376504320 ⟨⟨156663679135, 156663679144⟩, ⟨151899213217, 161494420766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 186122240 187432960 376504320 382074880 ⟨⟨159978325097, 159978325099⟩, ⟨155171702568, 164851560642⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 187432960 188743680 376504320 382074880 ⟨⟨158779161515, 158779161523⟩, ⟨153998995629, 163625494467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 183500800 184811520 382074880 387645440 ⟨⟨164545626832, 164545626840⟩, ⟨159669737060, 169488905418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 184811520 186122240 382074880 387645440 ⟨⟨163320448921, 163320448929⟩, ⟨158471488149, 168236350249⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 183500800 184811520 387645440 393216000 ⟨⟨166689943232, 166689943240⟩, ⟨161798468879, 171648675523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 184811520 186122240 387645440 393216000 ⟨⟨165452003594, 165452003603⟩, ⟨160587456921, 170383366479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 186122240 187432960 382074880 387645440 ⟨⟨162101901825, 162101901829⟩, ⟨157279634310, 166990665930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 187432960 188743680 382074880 387645440 ⟨⟨160889896212, 160889896220⟩, ⟨156094089483, 165751759818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 186122240 187432960 387645440 393216000 ⟨⟨164220699709, 164220699713⟩, ⟨159382846972, 169124931075⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 187432960 188743680 387645440 393216000 ⟨⟨162995942605, 162995942614⟩, ⟨158184553279, 167873277085⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 183500800 188743680 370933760 393216000 t = true :=
  ⟨_, (join_sr (m := 382074880) (by decide) (join_su (m := 186122240) (by decide) (join_sr (m := 376504320) (by decide) (join_su (m := 184811520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 184811520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 376504320) (by decide) (join_su (m := 187432960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 187432960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 186122240) (by decide) (join_sr (m := 387645440) (by decide) (join_su (m := 184811520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 184811520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 387645440) (by decide) (join_su (m := 187432960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 187432960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/32 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (283/640 : ℝ) (15/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  have e3 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

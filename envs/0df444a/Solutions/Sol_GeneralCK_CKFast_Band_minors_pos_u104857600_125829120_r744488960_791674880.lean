-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_125829120_r744488960_791674880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:52:13.354245+00:00
-- url     : https://prove2.me/submissions/1987d79d-2897-4948-aba5-c53c209fc0c7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 3/20]`, `ρ ∈ [71/80, 151/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 110100480 744488960 756285440 ⟨⟨421260141718, 421260141731⟩, ⟨396542064092, 446547560591⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 104857600 110100480 756285440 768081920 ⟨⟨426290161702, 426290161717⟩, ⟨401515392979, 451617640865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 110100480 115343360 744488960 756285440 ⟨⟨411884904517, 411884904530⟩, ⟨387547583950, 436804503598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 110100480 115343360 756285440 768081920 ⟨⟨416865706774, 416865706789⟩, ⟨392465710175, 441832326865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 104857600 110100480 768081920 779878400 ⟨⟨431304239349, 431304239363⟩, ⟨406473049935, 456671506196⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 104857600 110100480 779878400 791674880 ⟨⟨436303164054, 436303164068⟩, ⟨411415797659, 461709966736⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 110100480 115343360 768081920 779878400 ⟨⟨421831082943, 421831082955⟩, ⟨397368720829, 446844393716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 110100480 115343360 779878400 791674880 ⟨⟨426781785267, 426781785280⟩, ⟨402257341382, 451841477999⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 115343360 120586240 744488960 756285440 ⟨⟨402670435939, 402670435943⟩, ⟨378705689001, 427229010173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 115343360 120586240 756285440 768081920 ⟨⟨407599185496, 407599185505⟩, ⟨383566219779, 432211273975⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 120586240 125829120 744488960 756285440 ⟨⟨393608312703, 393608312715⟩, ⟨370008402606, 417812333436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 120586240 125829120 756285440 768081920 ⟨⟨398482348705, 398482348717⟩, ⟨374809096207, 422745931873⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 115343360 120586240 768081920 779878400 ⟨⟨412513042151, 412513042158⟩, ⟨388412198542, 437178268554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 115343360 120586240 779878400 791674880 ⟨⟨417412721490, 417412721497⟩, ⟨393244314326, 442130731554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 120586240 125829120 768081920 779878400 ⟨⟨403342037520, 403342037532⟩, ⟨379595805224, 427664771354⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 120586240 125829120 779878400 791674880 ⟨⟨408188058721, 408188058733⟩, ⟨384369183134, 432569553622⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 125829120 744488960 791674880 t = true :=
  ⟨_, (join_su (m := 115343360) (by decide) (join_sr (m := 768081920) (by decide) (join_su (m := 110100480) (by decide) (join_sr (m := 756285440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 756285440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 110100480) (by decide) (join_sr (m := 779878400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 779878400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 768081920) (by decide) (join_su (m := 120586240) (by decide) (join_sr (m := 756285440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 756285440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 120586240) (by decide) (join_sr (m := 779878400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 779878400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (71/80 : ℝ) (151/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((744488960 : ℤ) : ℝ) / (D : ℝ)) = (71/80 : ℝ) := by norm_num [D]
  have e3 : (((791674880 : ℤ) : ℝ) / (D : ℝ)) = (151/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

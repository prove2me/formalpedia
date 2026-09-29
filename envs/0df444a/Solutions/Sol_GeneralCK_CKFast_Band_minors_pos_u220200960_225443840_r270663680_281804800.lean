-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_225443840_r270663680_281804800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:51:50.49498+00:00
-- url     : https://prove2.me/submissions/11b0d4ee-a82f-47bb-9568-1d877e12cc06

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 43/160]`, `ρ ∈ [413/1280, 43/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 221511680 270663680 273448960 ⟨⟨95587120014, 95587120021⟩, ⟨92278157823, 98935303713⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 221511680 273448960 276234240 ⟨⟨96514182671, 96514182677⟩, ⟨93197984388, 99869630018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 221511680 222822400 270663680 273448960 ⟨⟨94785910533, 94785910540⟩, ⟨91491611473, 98119188773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 221511680 222822400 273448960 276234240 ⟨⟨95705999329, 95705999335⟩, ⟨92404490615, 99046515704⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 221511680 276234240 279019520 ⟨⟨97440373526, 97440373532⟩, ⟨94116945061, 100803078371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 221511680 279019520 281804800 ⟨⟨98365697183, 98365697189⟩, ⟨95035044407, 101735653408⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 221511680 222822400 276234240 279019520 ⟨⟨96625236056, 96625236063⟩, ⟨93316523322, 99972984697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 221511680 222822400 279019520 281804800 ⟨⟨97543625188, 97543625195⟩, ⟨94227714034, 100898600254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 222822400 224133120 270663680 273448960 ⟨⟨93988829121, 93988829129⟩, ⟨90709058408, 97307339517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 222822400 224133120 273448960 276234240 ⟨⟨94901961624, 94901961630⟩, ⟨91615007880, 98227684431⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 224133120 225443840 270663680 273448960 ⟨⟨93195818450, 93195818457⟩, ⟨89930443185, 96499696682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 224133120 225443840 273448960 276234240 ⟨⟨94102012104, 94102012110⟩, ⟨90829480611, 97413076820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 222822400 224133120 276234240 279019520 ⟨⟨95814261434, 95814261442⟩, ⟨92520130025, 99147191057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 222822400 224133120 279019520 281804800 ⟨⟨96725732899, 96725732906⟩, ⟨93424429155, 100065863769⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224133120 225443840 276234240 279019520 ⟨⟨95007392093, 95007392099⟩, ⟨91727709471, 98325637967⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 224133120 225443840 279019520 281804800 ⟨⟨95911962639, 95911962645⟩, ⟨92625133960, 99237384371⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 225443840 270663680 281804800 t = true :=
  ⟨_, (join_su (m := 222822400) (by decide) (join_sr (m := 276234240) (by decide) (join_su (m := 221511680) (by decide) (join_sr (m := 273448960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 273448960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 221511680) (by decide) (join_sr (m := 279019520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 279019520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 276234240) (by decide) (join_su (m := 224133120) (by decide) (join_sr (m := 273448960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 273448960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 224133120) (by decide) (join_sr (m := 279019520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 279019520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (413/1280 : ℝ) (43/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  have e3 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

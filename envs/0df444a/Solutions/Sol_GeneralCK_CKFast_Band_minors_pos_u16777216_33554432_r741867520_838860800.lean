-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_33554432_r741867520_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:34:29.438964+00:00
-- url     : https://prove2.me/submissions/b78fe08e-e26f-48e9-a90d-5866bee91dfd

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 1/25]`, `ρ ∈ [283/320, 1]` by 16 cells of the computing
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
theorem cell0 : cellOK 16777216 20971520 741867520 766115840 ⟨⟨621033231075, 621033231092⟩, ⟨583853236819, 657928099422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 20971520 25165824 741867520 766115840 ⟨⟨608733106879, 608733106895⟩, ⟨572313243972, 644997722636⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 16777216 20971520 766115840 790364160 ⟨⟨631587830683, 631587830700⟩, ⟨594818552102, 667988178497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 20971520 25165824 766115840 790364160 ⟨⟨619378062296, 619378062312⟩, ⟨583328693310, 655189591085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 25165824 29360128 741867520 766115840 ⟨⟨596960162624, 596960162642⟩, ⟨561232399591, 632635238226⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 29360128 33554432 741867520 766115840 ⟨⟨585634509227, 585634509245⟩, ⟨550550511375, 620750638935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 25165824 29360128 766115840 790364160 ⟨⟨607678682606, 607678682622⟩, ⟨572284268374, 642939287943⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 29360128 33554432 766115840 790364160 ⟨⟨596411797478, 596411797493⟩, ⟨561626586667, 631149673174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 16777216 20971520 790364160 814612480 ⟨⟨642091543097, 642091543114⟩, ⟨605713082840, 678020820134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 20971520 25165824 790364160 814612480 ⟨⟨629967158058, 629967158074⟩, ⟨594270618023, 665346617711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 16777216 20971520 814612480 838860800 ⟨⟨652553255931, 652553255946⟩, ⟨616547050718, 688033058807⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 20971520 25165824 814612480 838860800 ⟨⟨640509561711, 640509561726⟩, ⟨605149301736, 675476371024⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 25165824 29360128 790364160 814612480 ⟨⟨618337215902, 618337215918⟩, ⟨583260492663, 653202159317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 29360128 33554432 790364160 814612480 ⟨⟨607125700600, 607125700617⟩, ⟨572625431966, 641502115221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 25165824 29360128 814612480 838860800 ⟨⟨628945123317, 628945123333⟩, ⟨594171359410, 663431838867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 29360128 33554432 814612480 838860800 ⟨⟨617785700160, 617785700174⟩, ⟨583557288889, 651816271779⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 33554432 741867520 838860800 t = true :=
  ⟨_, (join_sr (m := 790364160) (by decide) (join_su (m := 25165824) (by decide) (join_sr (m := 766115840) (by decide) (join_su (m := 20971520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 20971520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 766115840) (by decide) (join_su (m := 29360128) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 29360128) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 25165824) (by decide) (join_sr (m := 814612480) (by decide) (join_su (m := 20971520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 20971520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 814612480) (by decide) (join_su (m := 29360128) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 29360128) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (283/320 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((741867520 : ℤ) : ℝ) / (D : ℝ)) = (283/320 : ℝ) := by norm_num [D]
  have e3 : (((838860800 : ℤ) : ℝ) / (D : ℝ)) = (1 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_222822400_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:57:09.766411+00:00
-- url     : https://prove2.me/submissions/71245913-b9ca-41d5-9cc2-a89283e7c73c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 17/64]`, `ρ ∈ [147/640, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 220856320 192675840 195461120 ⟨⟨69405949492, 69405949497⟩, ⟨67562152327, 71263616906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220856320 221511680 192675840 195461120 ⟨⟨69106384286, 69106384289⟩, ⟨67267470991, 70959111113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 220200960 220856320 195461120 198246400 ⟨⟨70361279118, 70361279125⟩, ⟨68513439607, 72222994802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 220856320 221511680 195461120 198246400 ⟨⟨70057915190, 70057915192⟩, ⟨68214969998, 71914680004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 221511680 222167040 192675840 195461120 ⟨⟨68807698114, 68807698121⟩, ⟨66973645640, 70655507780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 222167040 222822400 192675840 195461120 ⟨⟨68509884448, 68509884453⟩, ⟨66680669918, 70352800191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 221511680 222167040 195461120 198246400 ⟨⟨69755437610, 69755437616⟩, ⟨67917363691, 71607274977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222167040 222822400 195461120 198246400 ⟨⟨69453839811, 69453839818⟩, ⟨67620614290, 71300772967⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 220200960 220856320 198246400 201031680 ⟨⟨71315593139, 71315593144⟩, ⟨69463716336, 73181351959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 220856320 221511680 198246400 201031680 ⟨⟨71008442478, 71008442481⟩, ⟨69161470340, 72869240253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 220200960 220856320 201031680 203816960 ⟨⟨72268896832, 72268896839⟩, ⟨70412987763, 74138693686⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 220856320 221511680 201031680 203816960 ⟨⟨71957971350, 71957971354⟩, ⟨70106977187, 73822797088⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 221511680 222167040 198246400 201031680 ⟨⟨70702185363, 70702185369⟩, ⟨68860094846, 72558045509⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 222167040 222822400 198246400 201031680 ⟨⟨70396815190, 70396815196⟩, ⟨68559583421, 72247760940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 221511680 222167040 201031680 203816960 ⟨⟨71647946496, 71647946502⟩, ⟨69801844198, 73507824528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 222167040 222822400 201031680 203816960 ⟨⟨71338815627, 71338815634⟩, ⟨69497582324, 73193769180⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 222822400 192675840 203816960 t = true :=
  ⟨_, (join_sr (m := 198246400) (by decide) (join_su (m := 221511680) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 220856320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 220856320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 195461120) (by decide) (join_su (m := 222167040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 222167040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 221511680) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 220856320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 220856320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 201031680) (by decide) (join_su (m := 222167040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 222167040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (17/64 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

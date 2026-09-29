-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u110100480_115343360_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:26:13.838839+00:00
-- url     : https://prove2.me/submissions/d5b892b3-632e-45c9-8573-031bdb9468ef

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/160, 11/80]`, `ρ ∈ [109/640, 59/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 110100480 111411200 142868480 145817600 ⟨⟨108393472530, 108393472540⟩, ⟨103362727428, 113517215410⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 110100480 111411200 145817600 148766720 ⟨⟨110351617573, 110351617583⟩, ⟨105309652637, 115486268271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 111411200 112721920 142868480 145817600 ⟨⟨107369777637, 107369777647⟩, ⟨102381933769, 112449273730⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 111411200 112721920 145817600 148766720 ⟨⟨109313358486, 109313358496⟩, ⟨104314286232, 114403784280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 110100480 111411200 148766720 151715840 ⟨⟨112301510922, 112301510932⟩, ⟨107248454178, 117446941287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 110100480 111411200 151715840 154664960 ⟨⟨114243247704, 114243247712⟩, ⟨109179224938, 119399331850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 111411200 112721920 148766720 151715840 ⟨⟨111248869778, 111248869786⟩, ⟨106238693934, 116350100285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 111411200 112721920 151715840 154664960 ⟨⟨113176403522, 113176403530⟩, ⟨108155246739, 118288315926⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 112721920 114032640 142868480 145817600 ⟨⟨106360304217, 106360304227⟩, ⟨101414561682, 111396385869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 112721920 114032640 145817600 148766720 ⟨⟨108289433588, 108289433596⟩, ⟨103332457643, 113336462768⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 114032640 115343360 142868480 145817600 ⟨⟨105364705046, 105364705050⟩, ⟨100460286247, 110358181233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 114032640 115343360 145817600 148766720 ⟨⟨107279494637, 107279494641⟩, ⟨102363840736, 112283932347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 112721920 114032640 148766720 151715840 ⟨⟨110210671284, 110210671295⟩, ⟨105242583570, 115268526104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 112721920 114032640 151715840 154664960 ⟨⟨112124106318, 112124106326⟩, ⟨107145026409, 117192666970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 114032640 115343360 148766720 151715840 ⟨⟨109186566304, 109186566308⟩, ⟨104259795849, 114201846682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 114032640 115343360 151715840 154664960 ⟨⟨111086006158, 111086006160⟩, ⟨106148235718, 116112012349⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 110100480 115343360 142868480 154664960 t = true :=
  ⟨_, (join_su (m := 112721920) (by decide) (join_sr (m := 148766720) (by decide) (join_su (m := 111411200) (by decide) (join_sr (m := 145817600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 145817600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 111411200) (by decide) (join_sr (m := 151715840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 151715840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 148766720) (by decide) (join_su (m := 114032640) (by decide) (join_sr (m := 145817600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 145817600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 114032640) (by decide) (join_sr (m := 151715840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 151715840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/160 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

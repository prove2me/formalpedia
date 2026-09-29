-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u120586240_125829120_r201850880_225443840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:36:07.972174+00:00
-- url     : https://prove2.me/submissions/35f9c574-894c-4d59-87ba-482d8f48d78c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/160, 3/20]`, `ρ ∈ [77/320, 43/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 120586240 121896960 201850880 207749120 ⟨⟨137104742870, 137104742872⟩, ⟨130916026622, 143418199517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 121896960 123207680 201850880 207749120 ⟨⟨135932555406, 135932555416⟩, ⟨129794127052, 142194143543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 120586240 121896960 207749120 213647360 ⟨⟨140532338028, 140532338033⟩, ⟨134323373474, 146865171117⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 121896960 123207680 207749120 213647360 ⟨⟨139338235195, 139338235205⟩, ⟨133179462887, 145619326961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 123207680 124518400 201850880 207749120 ⟨⟨134773642463, 134773642472⟩, ⟨128684721398, 140984173939⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 124518400 125829120 201850880 207749120 ⟨⟨133627727223, 133627727233⟩, ⟨127587551297, 139787994606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 123207680 124518400 207749120 213647360 ⟨⟨138157499974, 138157499983⟩, ⟨132048147709, 144387652810⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 124518400 125829120 207749120 213647360 ⟨⟨136989855975, 136989855985⟩, ⟨130929169643, 143169853398⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 120586240 121896960 213647360 219545600 ⟨⟨143937801233, 143937801238⟩, ⟨137708977557, 150289623661⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 121896960 123207680 213647360 219545600 ⟨⟨142722219637, 142722219645⟩, ⟨136543484450, 149022435683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 120586240 121896960 219545600 225443840 ⟨⟨147321570599, 147321570603⟩, ⟨141073265183, 153692007174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 121896960 123207680 219545600 225443840 ⟨⟨146084934257, 146084934267⟩, ⟨139886605877, 152403906735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 123207680 124518400 213647360 219545600 ⟨⟨141520090432, 141520090440⟩, ⟨135390680037, 147769492955⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 124518400 125829120 213647360 219545600 ⟨⟨140331137825, 140331137833⟩, ⟨134250306251, 146530501205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 123207680 124518400 219545600 225443840 ⟨⟨144861827154, 144861827162⟩, ⟨138712720703, 151130118792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 124518400 125829120 219545600 225443840 ⟨⟨143651974237, 143651974245⟩, ⟨137551351977, 149870350214⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 120586240 125829120 201850880 225443840 t = true :=
  ⟨_, (join_sr (m := 213647360) (by decide) (join_su (m := 123207680) (by decide) (join_sr (m := 207749120) (by decide) (join_su (m := 121896960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 121896960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 207749120) (by decide) (join_su (m := 124518400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 124518400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 123207680) (by decide) (join_sr (m := 219545600) (by decide) (join_su (m := 121896960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 121896960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 219545600) (by decide) (join_su (m := 124518400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 124518400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/160 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (77/320 : ℝ) (43/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e3 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

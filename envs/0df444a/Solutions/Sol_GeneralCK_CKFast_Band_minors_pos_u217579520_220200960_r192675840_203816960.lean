-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u217579520_220200960_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:38:00.040389+00:00
-- url     : https://prove2.me/submissions/169d876b-6749-4ef6-931b-c11537ff83b4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [83/320, 21/80]`, `ρ ∈ [147/640, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 217579520 218234880 192675840 195461120 ⟨⟨70613133342, 70613133345⟩, ⟨68749566591, 72490800979⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 218234880 218890240 192675840 195461120 ⟨⟨70309985514, 70309985521⟩, ⟨68451396640, 72182617045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 217579520 218234880 195461120 198246400 ⟨⟨71583731804, 71583731807⟩, ⟨69716080929, 73465488787⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 218234880 218890240 195461120 198246400 ⟨⟨71276755598, 71276755603⟩, ⟨69414093039, 73153466213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 218890240 219545600 192675840 195461120 ⟨⟨70007743430, 70007743436⟩, ⟨68154108656, 71875363012⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 219545600 220200960 192675840 195461120 ⟨⟨69706400324, 69706400331⟩, ⟨67857696059, 71569031929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 218890240 219545600 195461120 198246400 ⟨⟨70970692608, 70970692613⟩, ⟨69112994592, 72842381007⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 219545600 220200960 195461120 198246400 ⟨⟨70665536028, 70665536035⟩, ⟨68812778970, 72532226179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 217579520 218234880 198246400 201031680 ⟨⟨72553265503, 72553265506⟩, ⟨70681535991, 74439106261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 218234880 218890240 198246400 201031680 ⟨⟨72242473386, 72242473393⟩, ⟨70375742521, 74123257629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 218234880 201031680 203816960 ⟨⟨73521740044, 73521740047⟩, ⟨71645937351, 75411659043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 218234880 218890240 201031680 203816960 ⟨⟨73207144407, 73207144414⟩, ⟨71336350580, 75091996850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 218890240 219545600 198246400 201031680 ⟨⟨71932601839, 71932601846⟩, ⟨70070845853, 73808353710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 219545600 220200960 198246400 201031680 ⟨⟨71623644019, 71623644024⟩, ⟨69766839325, 73494387475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 218890240 219545600 201031680 203816960 ⟨⟨72893476570, 72893476577⟩, ⟨71027667848, 74773286593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 219545600 220200960 201031680 203816960 ⟨⟨72580729653, 72580729658⟩, ⟨70719882455, 74455521206⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 217579520 220200960 192675840 203816960 t = true :=
  ⟨_, (join_sr (m := 198246400) (by decide) (join_su (m := 218890240) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 218234880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 218234880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 195461120) (by decide) (join_su (m := 219545600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 219545600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 218890240) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 218234880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 218234880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 201031680) (by decide) (join_su (m := 219545600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 219545600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (83/320 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

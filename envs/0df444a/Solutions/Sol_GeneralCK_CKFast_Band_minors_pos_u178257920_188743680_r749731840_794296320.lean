-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_188743680_r749731840_794296320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:26:59.461989+00:00
-- url     : https://prove2.me/submissions/a93320c1-633f-4489-b86d-74cdd9b5c0b1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 9/40]`, `ρ ∈ [143/160, 303/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 180879360 749731840 760872960 ⟨⟨305778510576, 305778510587⟩, ⟨294033427831, 317745589248⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 180879360 183500800 749731840 760872960 ⟨⟨301886194722, 301886194732⟩, ⟨290240602438, 313753686429⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 178257920 180879360 760872960 772014080 ⟨⟨309699023410, 309699023422⟩, ⟨297902149173, 321715860512⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 180879360 183500800 760872960 772014080 ⟨⟨305770846113, 305770846124⟩, ⟨294072979432, 317688683573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 183500800 186122240 749731840 760872960 ⟨⟨298015210888, 298015210899⟩, ⟨286468348591, 309783829326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 186122240 188743680 749731840 760872960 ⟨⟨294165108023, 294165108033⟩, ⟨282716225528, 305835558302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 183500800 186122240 760872960 772014080 ⟨⟨301863694516, 301863694526⟩, ⟨290264108839, 313683209811⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 186122240 188743680 760872960 772014080 ⟨⟨297977126005, 297977126015⟩, ⟨286475104233, 309698988879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 178257920 180879360 772014080 783155200 ⟨⟨313612069573, 313612069584⟩, ⟨301763556101, 325678486426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 180879360 183500800 772014080 783155200 ⟨⟨309648248083, 309648248094⟩, ⟨297898253701, 321616258073⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 178257920 180879360 783155200 794296320 ⟨⟨317517945464, 317517945475⟩, ⟨305617937459, 329633770600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 180879360 183500800 783155200 794296320 ⟨⟨313518686933, 313518686943⟩, ⟨301716704263, 325536703170⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 183500800 186122240 772014080 783155200 ⟨⟨305705143026, 305705143036⟩, ⟨294052974902, 317575387661⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 186122240 188743680 772014080 783155200 ⟨⟨301782320134, 301782320145⟩, ⟨290227294083, 313555434024⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 183500800 186122240 783155200 794296320 ⟨⟨309539832847, 309539832858⟩, ⟨297835216203, 321460645986⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 186122240 188743680 783155200 794296320 ⟨⟨305580957201, 305580957211⟩, ⟨293973055132, 317405166945⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 188743680 749731840 794296320 t = true :=
  ⟨_, (join_sr (m := 772014080) (by decide) (join_su (m := 183500800) (by decide) (join_sr (m := 760872960) (by decide) (join_su (m := 180879360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 180879360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 760872960) (by decide) (join_su (m := 186122240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 186122240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 183500800) (by decide) (join_sr (m := 783155200) (by decide) (join_su (m := 180879360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 180879360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 783155200) (by decide) (join_su (m := 186122240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 186122240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (143/160 : ℝ) (303/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((749731840 : ℤ) : ℝ) / (D : ℝ)) = (143/160 : ℝ) := by norm_num [D]
  have e3 : (((794296320 : ℤ) : ℝ) / (D : ℝ)) = (303/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

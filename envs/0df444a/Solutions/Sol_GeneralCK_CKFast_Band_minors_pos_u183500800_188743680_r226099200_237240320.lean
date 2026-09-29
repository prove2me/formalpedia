-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u183500800_188743680_r226099200_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:18:33.949005+00:00
-- url     : https://prove2.me/submissions/2f99ef9a-3d9d-4d88-8d17-857d55edf5b8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/32, 9/40]`, `ρ ∈ [69/256, 181/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 183500800 184811520 226099200 228884480 ⟨⟨101658439372, 101658439380⟩, ⟨98003312765, 105361056796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 183500800 184811520 228884480 231669760 ⟨⟨102815261651, 102815261659⟩, ⟨99151997621, 106526011512⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 184811520 186122240 226099200 228884480 ⟨⟨100838800147, 100838800155⟩, ⟨97202711971, 104522005345⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 184811520 186122240 228884480 231669760 ⟨⟨101987559171, 101987559179⟩, ⟨98343358575, 105678873664⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 183500800 184811520 231669760 234455040 ⟨⟨103970320899, 103970320905⟩, ⟨100298937733, 107689184508⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 183500800 184811520 234455040 237240320 ⟨⟨105123628217, 105123628225⟩, ⟨101444144069, 108850587022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 184811520 186122240 231669760 234455040 ⟨⟨103134592086, 103134592092⟩, ⟨99482296806, 106833997738⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 184811520 186122240 234455040 237240320 ⟨⟨104279909681, 104279909689⟩, ⟨100619537326, 107987388494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 186122240 187432960 226099200 228884480 ⟨⟨100024947160, 100024947164⟩, ⟨96407684089, 103688958774⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 186122240 187432960 228884480 231669760 ⟨⟨101165672885, 101165672888⟩, ⟨97540322788, 104837770206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 187432960 188743680 226099200 228884480 ⟨⟨99216790085, 99216790091⟩, ⟨95618142401, 102861823060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 187432960 188743680 228884480 231669760 ⟨⟨100349512252, 100349512258⟩, ⟨96742803310, 104002606925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 186122240 187432960 231669760 234455040 ⟨⟨102304708751, 102304708753⟩, ⟨98671288825, 105984874194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 186122240 187432960 234455040 237240320 ⟨⟨103442065249, 103442065252⟩, ⟨99800592568, 107130281347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 187432960 188743680 231669760 234455040 ⟨⟨101480580153, 101480580160⟩, ⟨97865826623, 105141719470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 187432960 188743680 234455040 237240320 ⟨⟨102610003988, 102610003996⟩, ⟨98987222417, 106279171013⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 183500800 188743680 226099200 237240320 t = true :=
  ⟨_, (join_su (m := 186122240) (by decide) (join_sr (m := 231669760) (by decide) (join_su (m := 184811520) (by decide) (join_sr (m := 228884480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 228884480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 184811520) (by decide) (join_sr (m := 234455040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 234455040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 231669760) (by decide) (join_su (m := 187432960) (by decide) (join_sr (m := 228884480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 228884480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 187432960) (by decide) (join_sr (m := 234455040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 234455040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/32 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (69/256 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_163840000_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:18:14.135776+00:00
-- url     : https://prove2.me/submissions/ca87331a-5d9f-4db5-b7b7-b11ab7767cb6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 25/128]`, `ρ ∈ [137/1280, 73/640]` by 14 cells of the computing
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
theorem cell0 : cellOK 162529280 162856960 89784320 91258880 ⟨⟨48923822951, 48923822957⟩, ⟨47799230509, 50054090414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 162856960 163184640 89784320 91258880 ⟨⟨48815004147, 48815004148⟩, ⟨47692336916, 49943328860⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 162529280 162856960 91258880 92733440 ⟨⟨49686693420, 49686693426⟩, ⟨48560538357, 50818520671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 162856960 163184640 91258880 92733440 ⟨⟨49576309454, 49576309457⟩, ⟨48452082380, 50706191221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 163184640 163512320 89784320 91258880 ⟨⟨48706469621, 48706469627⟩, ⟨47585720979, 49832858301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 163512320 163840000 89784320 91258880 ⟨⟨48598217951, 48598217957⟩, ⟨47479381315, 49722677263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 163184640 163512320 91258880 92733440 ⟨⟨49466213103, 49466213109⟩, ⟨48343907394, 50594156105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 163512320 163840000 91258880 92733440 ⟨⟨49356402929, 49356402935⟩, ⟨48236011995, 50482413836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 162529280 162856960 92733440 94208000 ⟨⟨50448564387, 50448564393⟩, ⟨49320851129, 51581946984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 162856960 163184640 92733440 94208000 ⟨⟨50336621114, 50336621117⟩, ⟨49210838591, 51468055527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 162529280 163184640 94208000 95682560 ⟨⟨51152654645, 51152654653⟩, ⟨49343269324, 52976425419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 163184640 163512320 92733440 94208000 ⟨⟨50224968757, 50224968765⟩, ⟨49101110340, 51354461709⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 163512320 163840000 92733440 94208000 ⟨⟨50113605867, 50113605873⟩, ⟨48991664961, 51241164029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 163184640 163840000 94208000 95682560 ⟨⟨50926249132, 50926249140⟩, ⟨49122357715, 52744446206⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 163840000 89784320 95682560 t = true :=
  ⟨_, (join_sr (m := 92733440) (by decide) (join_su (m := 163184640) (by decide) (join_sr (m := 91258880) (by decide) (join_su (m := 162856960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 162856960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 91258880) (by decide) (join_su (m := 163512320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 163512320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 163184640) (by decide) (join_sr (m := 94208000) (by decide) (join_su (m := 162856960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 94208000) (by decide) (join_su (m := 163512320) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (25/128 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((163840000 : ℤ) : ℝ) / (D : ℝ)) = (25/128 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

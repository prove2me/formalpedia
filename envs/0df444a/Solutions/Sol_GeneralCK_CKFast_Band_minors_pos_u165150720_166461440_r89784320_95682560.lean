-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u165150720_166461440_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:20:04.597991+00:00
-- url     : https://prove2.me/submissions/b6dc3ccf-2ac5-4da9-8a0a-e97bbd88a907

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [63/320, 127/640]`, `ρ ∈ [137/1280, 73/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 165150720 165478400 89784320 91258880 ⟨⟨48061153072, 48061153079⟩, ⟨46951778904, 49176064368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 165478400 165806080 89784320 91258880 ⟨⟨47954569052, 47954569058⟩, ⟨46847068114, 49067590256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 165150720 165478400 91258880 92733440 ⟨⟨48811594874, 48811594882⟩, ⟨47700680206, 49928044179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 165478400 165806080 91258880 92733440 ⟨⟨48703471991, 48703471999⟩, ⟨47594433303, 49818028498⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 165806080 166133760 89784320 91258880 ⟨⟨47848258146, 47848258152⟩, ⟨46742624098, 48959395680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 166133760 166461440 89784320 91258880 ⟨⟨47742219000, 47742219002⟩, ⟨46638445537, 48851479249⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 165806080 166133760 91258880 92733440 ⟨⟨48595625449, 48595625456⟩, ⟨47488456393, 49708295584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 166133760 166461440 91258880 92733440 ⟨⟨48488053881, 48488053884⟩, ⟨47382748149, 49598844030⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 165150720 165478400 92733440 94208000 ⟨⟨49561083065, 49561083071⟩, ⟨48448632054, 50679066206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 165478400 165806080 92733440 94208000 ⟨⟨49451426907, 49451426913⟩, ⟨48340854589, 50567514575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 165150720 165478400 94208000 95682560 ⟨⟨50309621422, 50309621428⟩, ⟨49195638205, 51429134251⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 165478400 165806080 94208000 95682560 ⟨⟨50198437544, 50198437550⟩, ⟨49086335701, 51316052260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 165806080 166133760 92733440 94208000 ⟨⟨49342050282, 49342050289⟩, ⟨48233350309, 50456248910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 166133760 166461440 92733440 94208000 ⟨⟨49232951812, 49232951815⟩, ⟨48126117870, 50345267788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 165806080 166133760 94208000 95682560 ⟨⟨50087536360, 50087536368⟩, ⟨48977309541, 51203259397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 166133760 166461440 94208000 95682560 ⟨⟨49976916480, 49976916483⟩, ⟨48868558367, 51090754230⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 165150720 166461440 89784320 95682560 t = true :=
  ⟨_, (join_sr (m := 92733440) (by decide) (join_su (m := 165806080) (by decide) (join_sr (m := 91258880) (by decide) (join_su (m := 165478400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 165478400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 91258880) (by decide) (join_su (m := 166133760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 166133760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 165806080) (by decide) (join_sr (m := 94208000) (by decide) (join_su (m := 165478400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 165478400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 94208000) (by decide) (join_su (m := 166133760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 166133760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (63/320 : ℝ) (127/640 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e1 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

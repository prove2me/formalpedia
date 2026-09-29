-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_141557760_r249036800_272629760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:43:26.56475+00:00
-- url     : https://prove2.me/submissions/327cca4a-3e06-4076-8a42-8e541ea6cbdb

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 27/160]`, `ρ ∈ [19/64, 13/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 137625600 249036800 254935040 ⟨⟨148753322782, 148753322790⟩, ⟨142960974384, 154648875681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 137625600 138936320 249036800 254935040 ⟨⟨147566692718, 147566692727⟩, ⟨141816065520, 153419434577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 136314880 137625600 254935040 260833280 ⟨⟨151793188209, 151793188219⟩, ⟨145982114009, 157706906901⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 137625600 138936320 254935040 260833280 ⟨⟨150588317178, 150588317186⟩, ⟨144818901160, 156459307782⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 138936320 140247040 249036800 254935040 ⟨⟨146391052357, 146391052366⟩, ⟨140681595933, 152201551402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 140247040 141557760 249036800 254935040 ⟨⟨145226202948, 145226202954⟩, ⟨139557377994, 150995015889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 138936320 140247040 254935040 260833280 ⟨⟨149394484175, 149394484184⟩, ⟨143666181524, 155223308726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 140247040 141557760 254935040 260833280 ⟨⟨148211491052, 148211491058⟩, ⟨142523767867, 153998700292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 136314880 137625600 260833280 266731520 ⟨⟨154817946733, 154817946741⟩, ⟨148988390142, 160749587487⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 137625600 138936320 260833280 266731520 ⟨⟨153595118175, 153595118182⟩, ⟨147807151850, 159484118539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 136314880 137625600 266731520 272629760 ⟨⟨157827859759, 157827859768⟩, ⟨151980058126, 163777184975⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 137625600 138936320 266731520 272629760 ⟨⟨156587350169, 156587350179⟩, ⟨150781066187, 162494127231⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 138936320 140247040 260833280 266731520 ⟨⟨152383371202, 152383371210⟩, ⟨146636455989, 158230286973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 140247040 141557760 260833280 266731520 ⟨⟨151182508340, 151182508343⟩, ⟨145476115790, 156987884252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 138936320 140247040 266731520 272629760 ⟨⟨155357961135, 155357961142⟩, ⟨149592661351, 161222739572⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 140247040 141557760 266731520 272629760 ⟨⟨154139495924, 154139495930⟩, ⟨148414657392, 159962814425⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 141557760 249036800 272629760 t = true :=
  ⟨_, (join_sr (m := 260833280) (by decide) (join_su (m := 138936320) (by decide) (join_sr (m := 254935040) (by decide) (join_su (m := 137625600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 137625600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 254935040) (by decide) (join_su (m := 140247040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 140247040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 138936320) (by decide) (join_sr (m := 266731520) (by decide) (join_su (m := 137625600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 137625600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 266731520) (by decide) (join_su (m := 140247040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 140247040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (27/160 : ℝ) →
    rho ∈ Set.Icc (19/64 : ℝ) (13/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e2 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e3 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

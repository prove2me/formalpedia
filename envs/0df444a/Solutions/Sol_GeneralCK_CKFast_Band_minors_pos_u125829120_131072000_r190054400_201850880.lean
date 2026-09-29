-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_131072000_r190054400_201850880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:33:53.926756+00:00
-- url     : https://prove2.me/submissions/68f62b70-c05b-4734-af0b-19476cc02ad1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 5/32]`, `ρ ∈ [29/128, 77/320]` by 14 cells of the computing
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
theorem cell0 : cellOK 125829120 127139840 190054400 193003520 ⟨⟨124901630169, 124901630179⟩, ⟨120169902523, 129709158444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 125829120 127139840 193003520 195952640 ⟨⟨126598298344, 126598298353⟩, ⟨121856790230, 131415417035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 127139840 128450560 190054400 193003520 ⟨⟨123830915805, 123830915811⟩, ⟨119133898135, 128602847467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 127139840 128450560 193003520 195952640 ⟨⟨125516282740, 125516282744⟩, ⟨120809474054, 130297823328⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 125829120 127139840 195952640 201850880 ⟨⟨129133212554, 129133212562⟩, ⟨123161987371, 135223792411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 127139840 128450560 195952640 201850880 ⟨⟨128034449435, 128034449440⟩, ⟨122110554249, 134076210962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 128450560 129761280 190054400 193003520 ⟨⟨122772171649, 122772171658⟩, ⟨118109318547, 127509069665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 128450560 129761280 193003520 195952640 ⟨⟨124446294889, 124446294897⟩, ⟨119773642651, 129192817649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 129761280 131072000 190054400 193003520 ⟨⟨121725150391, 121725150401⟩, ⟨117095929253, 126427564447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 129761280 131072000 193003520 195952640 ⟨⟨123388087349, 123388087358⟩, ⟨118749061268, 128100139394⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 128450560 129761280 195952640 198901760 ⟨⟨126115245408, 126115245416⟩, ⟨121432865122, 130871321404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 128450560 129761280 198901760 201850880 ⟨⟨127779072572, 127779072582⟩, ⟨123087034367, 132544631270⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 129761280 131072000 195952640 198901760 ⟨⟨125045956543, 125045956550⟩, ⟨120397194954, 129767576697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 129761280 131072000 198901760 201850880 ⟨⟨126698805890, 126698805900⟩, ⟨122040377304, 131429925214⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 131072000 190054400 201850880 t = true :=
  ⟨_, (join_su (m := 128450560) (by decide) (join_sr (m := 195952640) (by decide) (join_su (m := 127139840) (by decide) (join_sr (m := 193003520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 193003520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 127139840) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 195952640) (by decide) (join_su (m := 129761280) (by decide) (join_sr (m := 193003520) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 193003520) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 129761280) (by decide) (join_sr (m := 198901760) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 198901760) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (5/32 : ℝ) →
    rho ∈ Set.Icc (29/128 : ℝ) (77/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e2 : (((190054400 : ℤ) : ℝ) / (D : ℝ)) = (29/128 : ℝ) := by norm_num [D]
  have e3 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

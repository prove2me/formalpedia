-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u233308160_234618880_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T10:57:46.61775+00:00
-- url     : https://prove2.me/submissions/c9735be6-ab13-4987-bf3d-b49b262edba6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [89/320, 179/640]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 233308160 233635840 136970240 138362880 ⟨⟨45614254368, 45614254370⟩, ⟨44776168231, 46455496402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 233635840 233963520 136970240 138362880 ⟨⟨45510681662, 45510681668⟩, ⟨44673657566, 46350855111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233308160 233635840 138362880 139755520 ⟨⟨46063700997, 46063700999⟩, ⟨45224637778, 46905921375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 233635840 233963520 138362880 139755520 ⟨⟨45959158434, 45959158439⟩, ⟨45121158777, 46800308711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 233963520 234291200 136970240 138362880 ⟨⟨45407260544, 45407260550⟩, ⟨44571296031, 46246367887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 234291200 234618880 136970240 138362880 ⟨⟨45303990435, 45303990440⟩, ⟨44469083051, 46142034143⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233963520 234291200 138362880 139755520 ⟨⟨45854768561, 45854768567⟩, ⟨45017830008, 46694851216⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 234291200 234618880 138362880 139755520 ⟨⟨45750530794, 45750530799⟩, ⟨44914650890, 46589548302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 233635840 139755520 141148160 ⟨⟨46512926557, 46512926559⟩, ⟨45672886703, 47356124824⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 233635840 233963520 139755520 141148160 ⟨⟨46407415539, 46407415544⟩, ⟨45568440766, 47249542194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 233308160 233635840 141148160 142540800 ⟨⟨46961931581, 46961931583⟩, ⟨46120915543, 47806107285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 233635840 233963520 141148160 142540800 ⟨⟨46855453505, 46855453512⟩, ⟨46015504060, 47698556095⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 233963520 234291200 139755520 141148160 ⟨⟨46302058304, 46302058311⟩, ⟨45464146151, 47143115830⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 234291200 234618880 139755520 141148160 ⟨⟨46196854269, 46196854275⟩, ⟨45360002278, 47036845141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 233963520 234291200 141148160 142540800 ⟨⟨46749130303, 46749130308⟩, ⟨45910244985, 47591162258⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 234291200 234618880 141148160 142540800 ⟨⟨46642961381, 46642961387⟩, ⟨45805137734, 47483925181⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 233308160 234618880 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 233963520) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 233635840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 233635840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 234291200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 234291200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 233963520) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 233635840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 233635840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 234291200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 234291200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (89/320 : ℝ) (179/640 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e1 : (((234618880 : ℤ) : ℝ) / (D : ℝ)) = (179/640 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

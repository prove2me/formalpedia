-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u222822400_225443840_r237240320_248381440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:30:04.584024+00:00
-- url     : https://prove2.me/submissions/7b58c525-2c92-4b0c-bae0-6a5bbebbc9ed

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/64, 43/160]`, `ρ ∈ [181/640, 379/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 222822400 223477760 237240320 240025600 ⟨⟨83142331664, 83142331670⟩, ⟨81254465958, 85043939317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 223477760 224133120 237240320 240025600 ⟨⟨82787270545, 82787270551⟩, ⟨80904353162, 84683877260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 223477760 240025600 242810880 ⟨⟨84067600093, 84067600100⟩, ⟨82175804963, 85973142560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 223477760 224133120 240025600 242810880 ⟨⟨83708944969, 83708944974⟩, ⟨81822107092, 85609477738⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 224133120 224788480 237240320 240025600 ⟨⟨82433164191, 82433164194⟩, ⟨80555172906, 84324792508⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 224788480 225443840 237240320 240025600 ⟨⟨82080005779, 82080005785⟩, ⟨80206918534, 83966678079⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 224133120 224788480 240025600 242810880 ⟨⟨83351250074, 83351250077⟩, ⟨81469347243, 85246795668⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 224788480 225443840 240025600 242810880 ⟨⟨82994508566, 82994508572⟩, ⟨81117518739, 84885089345⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 222822400 223477760 242810880 245596160 ⟨⟨84991976971, 84991976978⟩, ⟨83096256643, 86901449950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 223477760 224133120 242810880 245596160 ⟨⟨84629738222, 84629738228⟩, ⟨82738983988, 86534192836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 222822400 223477760 245596160 248381440 ⟨⟨85915466912, 85915466918⟩, ⟨84015825588, 87828866126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 223477760 224133120 245596160 248381440 ⟨⟨85549654854, 85549654860⟩, ⟨83654988376, 87458027126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 224133120 224788480 242810880 245596160 ⟨⟨84268465073, 84268465076⟩, ⟨82382654744, 86167923823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 224788480 225443840 242810880 245596160 ⟨⟨83908150657, 83908150664⟩, ⟨82027262208, 85802635883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224133120 224788480 245596160 248381440 ⟨⟨85184813671, 85184813672⟩, ⟨83295099866, 87088181478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 224788480 225443840 245596160 248381440 ⟨⟨84820936469, 84820936475⟩, ⟨82936153334, 86719322132⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 222822400 225443840 237240320 248381440 t = true :=
  ⟨_, (join_sr (m := 242810880) (by decide) (join_su (m := 224133120) (by decide) (join_sr (m := 240025600) (by decide) (join_su (m := 223477760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 223477760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 240025600) (by decide) (join_su (m := 224788480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 224788480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 224133120) (by decide) (join_sr (m := 245596160) (by decide) (join_su (m := 223477760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 223477760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 245596160) (by decide) (join_su (m := 224788480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 224788480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/64 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (181/640 : ℝ) (379/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e3 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

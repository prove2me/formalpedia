-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_237240320_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:35:06.837651+00:00
-- url     : https://prove2.me/submissions/47aeb7bc-2721-4591-be50-c0980d60532e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 181/640]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 236257280 131399680 132792320 ⟨⟨43020900586, 43020900592⟩, ⟨42195106293, 43849793726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 236257280 236584960 131399680 132792320 ⟨⟨42922382586, 42922382593⟩, ⟨42097624827, 43750232795⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 235929600 236257280 132792320 134184960 ⟨⟨43463464267, 43463464273⟩, ⟨42636703396, 44293325313⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 236257280 236584960 132792320 134184960 ⟨⟨43363979712, 43363979717⟩, ⟨42538256903, 44192796301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 236584960 236912640 131399680 132792320 ⟨⟨42824007247, 42824007249⟩, ⟨42000283642, 43650816918⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 236912640 237240320 131399680 132792320 ⟨⟨42725774016, 42725774023⟩, ⟨41903082199, 43551545549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 236584960 236912640 132792320 134184960 ⟨⟨43264638918, 43264638920⟩, ⟨42439951794, 44092413449⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 236912640 237240320 132792320 134184960 ⟨⟨43165441333, 43165441339⟩, ⟨42341787523, 43992176202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 236257280 134184960 135577600 ⟨⟨43905815880, 43905815886⟩, ⟨43078088838, 44736644418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 236257280 236584960 134184960 135577600 ⟨⟨43805366128, 43805366133⟩, ⟨42978678674, 44635148691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 235929600 236257280 135577600 136970240 ⟨⟨44347955928, 44347955935⟩, ⟨43519263123, 45179751549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 236257280 236584960 135577600 136970240 ⟨⟨44246542337, 44246542343⟩, ⟨43418890640, 45077290470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 236584960 236912640 134184960 135577600 ⟨⟨43705061234, 43705061237⟩, ⟨42879410987, 44533800221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 236912640 237240320 134184960 135577600 ⟨⟨43604900640, 43604900646⟩, ⟨42780285229, 44432598452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 236584960 236912640 135577600 136970240 ⟨⟨44145274691, 44145274693⟩, ⟨43318661719, 44974977737⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 236912640 237240320 135577600 136970240 ⟨⟨44044152431, 44044152436⟩, ⟨43218575810, 44872812791⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 237240320 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 236584960) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 236257280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 236257280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 236912640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 236912640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 236584960) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 236257280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 236257280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 236912640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 236912640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (181/640 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

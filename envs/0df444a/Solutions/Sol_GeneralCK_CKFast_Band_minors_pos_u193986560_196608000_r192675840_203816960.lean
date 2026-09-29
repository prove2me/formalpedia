-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_196608000_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:06:03.129417+00:00
-- url     : https://prove2.me/submissions/48b41794-d414-4ee0-9566-5a50cfda64b9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 15/64]`, `ρ ∈ [147/640, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 193986560 194641920 192675840 195461120 ⟨⟨82192060784, 82192060791⟩, ⟨80131738513, 84268869258⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 194641920 195297280 192675840 195461120 ⟨⟨81851243241, 81851243244⟩, ⟨79796894820, 83922003098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 193986560 194641920 195461120 198246400 ⟨⟨83305806656, 83305806662⟩, ⟨81241031547, 85387064526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 194641920 195297280 195461120 198246400 ⟨⟨82960863899, 82960863902⟩, ⟨80902072543, 85036063557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 195297280 195952640 192675840 195461120 ⟨⟨81511620703, 81511620710⟩, ⟨79463214286, 83576364337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 195952640 196608000 192675840 195461120 ⟨⟨81173183746, 81173183752⟩, ⟨79130687749, 83231943271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 195297280 195952640 195461120 198246400 ⟨⟨82617125152, 82617125160⟩, ⟨80564285733, 84686298962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 195952640 196608000 195461120 198246400 ⟨⟨82274580948, 82274580955⟩, ⟨80227661910, 84337760988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 194641920 198246400 201031680 ⟨⟨84417947433, 84417947440⟩, ⟨82348729938, 86503644136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 194641920 195297280 198246400 201031680 ⟨⟨84068897152, 84068897155⟩, ⟨82005673147, 86148526217⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 193986560 194641920 201031680 203816960 ⟨⟨85528492706, 85528492713⟩, ⟨83454843200, 87618617753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 194641920 195297280 201031680 203816960 ⟨⟨85175352451, 85175352454⟩, ⟨83107706005, 87259400602⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 195297280 195952640 198246400 201031680 ⟨⟨83721059718, 83721059724⟩, ⟨81663797415, 85794653473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 195952640 196608000 198246400 201031680 ⟨⟨83374425619, 83374425626⟩, ⟨81323093494, 85442016110⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 195297280 195952640 201031680 203816960 ⟨⟨84823433712, 84823433718⟩, ⟨82761758571, 86901437255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 195952640 196608000 201031680 203816960 ⟨⟨84472726933, 84472726940⟩, ⟨82416991605, 86544717879⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 196608000 192675840 203816960 t = true :=
  ⟨_, (join_sr (m := 198246400) (by decide) (join_su (m := 195297280) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 194641920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 194641920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 195461120) (by decide) (join_su (m := 195952640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 195952640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 195297280) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 194641920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 194641920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 201031680) (by decide) (join_su (m := 195952640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 195952640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (15/64 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((196608000 : ℤ) : ℝ) / (D : ℝ)) = (15/64 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

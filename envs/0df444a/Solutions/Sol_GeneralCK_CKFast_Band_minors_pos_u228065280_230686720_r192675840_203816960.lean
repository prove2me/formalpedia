-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u228065280_230686720_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:59:49.816725+00:00
-- url     : https://prove2.me/submissions/c6505dce-c61d-49f0-aa96-36911e809ce9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [87/320, 11/40]`, `ρ ∈ [147/640, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 228065280 228720640 192675840 195461120 ⟨⟨65867773322, 65867773329⟩, ⟨64081099141, 67667660940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 228720640 229376000 192675840 195461120 ⟨⟨65578337361, 65578337366⟩, ⟨63796281689, 67373553993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 228065280 228720640 195461120 198246400 ⟨⟨66777992542, 66777992549⟩, ⟨64987401414, 68581804889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 228720640 229376000 195461120 198246400 ⟨⟨66484843089, 66484843094⟩, ⟨64698880910, 68283974151⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 229376000 230031360 192675840 195461120 ⟨⟨65289705590, 65289705597⟩, ⟨63512247379, 67080272620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230031360 230686720 192675840 195461120 ⟨⟨65001872109, 65001872114⟩, ⟨63228990467, 66787810758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 229376000 230031360 195461120 198246400 ⟨⟨66192504683, 66192504688⟩, ⟨64411150401, 67986975843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 230031360 230686720 195461120 198246400 ⟨⟨65900971383, 65900971389⟩, ⟨64124204104, 67690803867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 228065280 228720640 198246400 201031680 ⟨⟨67687332515, 67687332521⟩, ⟨65892828316, 69495065649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 228720640 229376000 198246400 201031680 ⟨⟨67390480218, 67390480225⟩, ⟨65600615318, 69193521861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 228720640 201031680 203816960 ⟨⟨68595797638, 68595797643⟩, ⟨66797384219, 70407447639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228720640 229376000 201031680 203816960 ⟨⟨68295253079, 68295253085⟩, ⟨66501489217, 70102201472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 229376000 230031360 198246400 201031680 ⟨⟨67094445718, 67094445725⟩, ⟨65309199061, 68892817251⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 230031360 230686720 198246400 201031680 ⟨⟨66799223039, 66799223045⟩, ⟨65018573727, 68592945687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 229376000 230031360 201031680 203816960 ⟨⟨67995532963, 67995532968⟩, ⟨66206397602, 69797801126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 230031360 230686720 201031680 203816960 ⟨⟨67696631275, 67696631282⟩, ⟨65912103516, 69494240436⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 228065280 230686720 192675840 203816960 t = true :=
  ⟨_, (join_sr (m := 198246400) (by decide) (join_su (m := 229376000) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 228720640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 228720640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 195461120) (by decide) (join_su (m := 230031360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 230031360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 229376000) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 228720640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 228720640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 201031680) (by decide) (join_su (m := 230031360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 230031360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (87/320 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

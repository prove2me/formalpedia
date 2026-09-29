-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_238551040_r248381440_259522560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:44:10.229056+00:00
-- url     : https://prove2.me/submissions/b28d0c6a-ee8a-4ba5-a25d-812d5f9ea2cc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 91/320]`, `ρ ∈ [379/1280, 99/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 236584960 248381440 251166720 ⟨⟨79628402252, 79628402258⟩, ⟨77820480787, 81449104184⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 236584960 237240320 248381440 251166720 ⟨⟨79277295153, 79277295160⟩, ⟨77473942884, 81093381689⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 235929600 236584960 251166720 253952000 ⟨⟨80480016252, 80480016259⟩, ⟨78668357061, 82304464058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 236584960 237240320 251166720 253952000 ⟨⟨80125453939, 80125453945⟩, ⟨78318372845, 81945277578⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 237240320 237895680 248381440 251166720 ⟨⟨78927035690, 78927035693⟩, ⟨77128233388, 80738526319⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 237895680 238551040 248381440 251166720 ⟨⟨78577617940, 78577617947⟩, ⟨76783346515, 80384532018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237240320 237895680 251166720 253952000 ⟨⟨79771743925, 79771743929⟩, ⟨77969221713, 81586962872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 237895680 238551040 251166720 253952000 ⟨⟨79418880267, 79418880274⟩, ⟨77620897856, 81229513866⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 236584960 253952000 256737280 ⟨⟨81330942303, 81330942310⟩, ⟨79515547939, 83159133372⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 236584960 237240320 253952000 256737280 ⟨⟨80972933147, 80972933154⟩, ⟨79162125712, 82796491346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 235929600 236584960 256737280 259522560 ⟨⟨82181183778, 82181183783⟩, ⟨80362056778, 84013115510⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 236584960 237240320 256737280 259522560 ⟨⟨81819736097, 81819736103⟩, ⟨80005204791, 83647026327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 237240320 237895680 253952000 256737280 ⟨⟨80615780873, 80615780876⟩, ⟨78809541165, 82434725664⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 237895680 238551040 253952000 256737280 ⟨⟨80259479518, 80259479525⟩, ⟨78457788467, 82073830231⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 237240320 237895680 256737280 259522560 ⟨⟨81459149804, 81459149807⟩, ⟨79649195001, 83281817979⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 237895680 238551040 256737280 259522560 ⟨⟨81099418912, 81099418919⟩, ⟨79294021557, 82917484351⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 238551040 248381440 259522560 t = true :=
  ⟨_, (join_sr (m := 253952000) (by decide) (join_su (m := 237240320) (by decide) (join_sr (m := 251166720) (by decide) (join_su (m := 236584960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 236584960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 251166720) (by decide) (join_su (m := 237895680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 237895680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 237240320) (by decide) (join_sr (m := 256737280) (by decide) (join_su (m := 236584960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 236584960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 256737280) (by decide) (join_su (m := 237895680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 237895680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (91/320 : ℝ) →
    rho ∈ Set.Icc (379/1280 : ℝ) (99/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e2 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  have e3 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

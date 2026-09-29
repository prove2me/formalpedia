-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_238551040_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:32:31.562324+00:00
-- url     : https://prove2.me/submissions/a80cd459-04e5-43d7-ba7f-6512602617a6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 91/320]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 236584960 214958080 217743360 ⟨⟨69354129268, 69354129275⟩, ⟨67591265131, 71129671496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 236584960 237240320 214958080 217743360 ⟨⟨69045156370, 69045156375⟩, ⟨67286749033, 70816194086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 235929600 236584960 217743360 220528640 ⟨⟨70214266407, 70214266413⟩, ⟨68447632733, 71993587025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 236584960 237240320 217743360 220528640 ⟨⟨69901733812, 69901733819⟩, ⟨68139566708, 71676540274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 237240320 237895680 214958080 217743360 ⟨⟨68736968643, 68736968646⟩, ⟨66982998810, 70503521428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 237895680 238551040 214958080 217743360 ⟨⟨68429560467, 68429560474⟩, ⟨66680008983, 70191647766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237240320 237895680 217743360 220528640 ⟨⟨69589992070, 69589992072⟩, ⟨67832272238, 71360303952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 237895680 238551040 217743360 220528640 ⟨⟨69279035528, 69279035535⟩, ⟨67525743814, 71044872273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 236584960 220528640 223313920 ⟨⟨71073674104, 71073674109⟩, ⟨69303273628, 72856770320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 236584960 237240320 220528640 223313920 ⟨⟨70757590811, 70757590817⟩, ⟨68991666597, 72536163300⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 235929600 236584960 223313920 226099200 ⟨⟨71932355891, 71932355896⟩, ⟨70158191332, 73719224928⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 236584960 237240320 223313920 226099200 ⟨⟨71612730844, 71612730851⟩, ⟨69843052167, 73395066659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 237240320 237895680 220528640 223313920 ⟨⟨70442303961, 70442303964⟩, ⟨68680836716, 72216372296⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 237895680 238551040 220528640 223313920 ⟨⟨70127807876, 70127807883⟩, ⟨68370778445, 71897391496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 237240320 237895680 223313920 226099200 ⟨⟨71293907745, 71293907748⟩, ⟨69528695657, 73071729904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 237895680 238551040 223313920 226099200 ⟨⟨70975880884, 70975880891⟩, ⟨69215116235, 72749208823⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 238551040 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 237240320) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 236584960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 236584960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 217743360) (by decide) (join_su (m := 237895680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 237895680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 237240320) (by decide) (join_sr (m := 223313920) (by decide) (join_su (m := 236584960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 236584960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 223313920) (by decide) (join_su (m := 237895680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 237895680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (91/320 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

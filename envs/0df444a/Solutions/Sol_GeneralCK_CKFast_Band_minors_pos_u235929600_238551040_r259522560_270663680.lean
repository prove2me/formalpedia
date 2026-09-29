-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_238551040_r259522560_270663680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:07:42.924519+00:00
-- url     : https://prove2.me/submissions/b29b0ab2-7ae9-41c4-9845-710d5ef89564

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 91/320]`, `ρ ∈ [99/320, 413/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 236584960 259522560 262307840 ⟨⟨83030744030, 83030744036⟩, ⟨81207886920, 84866413842⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 236584960 237240320 259522560 262307840 ⟨⟨82665866096, 82665866103⟩, ⟨80847613376, 84496885845⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 235929600 236584960 262307840 265093120 ⟨⟨83879626407, 83879626414⟩, ⟨82053041696, 85719031731⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 236584960 237240320 262307840 265093120 ⟨⟨83511326440, 83511326446⟩, ⟨81689354745, 85346073207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 237240320 237895680 259522560 262307840 ⟨⟨82301853975, 82301853977⟩, ⟨80488186465, 84128243090⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 237895680 238551040 259522560 262307840 ⟨⟨81938701661, 81938701668⟩, ⟨80129600322, 83760479446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237240320 237895680 262307840 265093120 ⟨⟨83143896631, 83143896634⟩, ⟨81326518790, 84974004256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 237895680 238551040 262307840 265093120 ⟨⟨82777330960, 82777330967⟩, ⟨80964527942, 84602818729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 236584960 265093120 267878400 ⟨⟨84727834238, 84727834245⟩, ⟨82897524422, 86570972519⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 236584960 237240320 265093120 267878400 ⟨⟨84356120409, 84356120416⟩, ⟨82530432167, 86194591709⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 235929600 236584960 267878400 270663680 ⟨⟨85575370845, 85575370851⟩, ⟨83741338403, 87422239543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 236584960 237240320 267878400 270663680 ⟨⟨85200251274, 85200251280⟩, ⟨83370848897, 87042444635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 237240320 237895680 265093120 267878400 ⟨⟨83985281008, 83985281011⟩, ⟨82164195192, 85819104722⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 237895680 238551040 265093120 267878400 ⟨⟨83615309996, 83615310002⟩, ⟨81798807593, 85444505395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 237240320 237895680 267878400 270663680 ⟨⟨84826010324, 84826010327⟩, ⟨83001218882, 86663547726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 237895680 238551040 267878400 270663680 ⟨⟨84452641940, 84452641945⟩, ⟨82632442433, 86285542633⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 238551040 259522560 270663680 t = true :=
  ⟨_, (join_sr (m := 265093120) (by decide) (join_su (m := 237240320) (by decide) (join_sr (m := 262307840) (by decide) (join_su (m := 236584960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 236584960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 262307840) (by decide) (join_su (m := 237895680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 237895680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 237240320) (by decide) (join_sr (m := 267878400) (by decide) (join_su (m := 236584960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 236584960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 267878400) (by decide) (join_su (m := 237895680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 237895680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (91/320 : ℝ) →
    rho ∈ Set.Icc (99/320 : ℝ) (413/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e2 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  have e3 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

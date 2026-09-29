-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_238551040_r281804800_292945920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:14:52.743558+00:00
-- url     : https://prove2.me/submissions/75ceec63-5a01-4e10-bb4b-828867c4eb7c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 91/320]`, `ρ ∈ [43/128, 447/1280]` by 14 cells of the computing
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
theorem cell0 : cellOK 235929600 236584960 281804800 284590080 ⟨⟨89803100760, 89803100766⟩, ⟨87950491890, 91668583952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 236584960 237240320 281804800 284590080 ⟨⟨89411072601, 89411072608⟩, ⟨87563135253, 91271839686⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 235929600 236584960 284590080 287375360 ⟨⟨90646678999, 90646679007⟩, ⟨88790362084, 92515877673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 236584960 237240320 284590080 287375360 ⟨⟨90251292811, 90251292817⟩, ⟨88399655510, 92115767421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 237240320 237895680 281804800 284590080 ⟨⟨89019942898, 89019942901⟩, ⟨87176658032, 90876013150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 237895680 238551040 281804800 284590080 ⟨⟨88629705515, 88629705521⟩, ⟨86791054223, 90481098088⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237240320 237895680 284590080 287375360 ⟨⟨89856808822, 89856808825⟩, ⟨88009832117, 91716578623⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 237895680 238551040 284590080 287375360 ⟨⟨89463220884, 89463220891⟩, ⟨87620885888, 91318305006⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 237240320 287375360 290160640 ⟨⟨91290127056, 91290127063⟩, ⟨88107221085, 94509744232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 235929600 237240320 290160640 292945920 ⟨⟨92130740121, 92130740128⟩, ⟨88940943605, 95357283888⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 237240320 237895680 287375360 290160640 ⟨⟨90693041897, 90693041899⟩, ⟨88842375605, 92556508938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 237895680 238551040 287375360 290160640 ⟨⟨90296111045, 90296111052⟩, ⟨88450094533, 92154884470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 237240320 237895680 290160640 292945920 ⟨⟨91528645249, 91528645252⟩, ⟨89674291607, 93395807234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 237895680 238551040 290160640 292945920 ⟨⟨91128379077, 91128379084⟩, ⟨89278683224, 92990839576⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 238551040 281804800 292945920 t = true :=
  ⟨_, (join_sr (m := 287375360) (by decide) (join_su (m := 237240320) (by decide) (join_sr (m := 284590080) (by decide) (join_su (m := 236584960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 236584960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 284590080) (by decide) (join_su (m := 237895680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 237895680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 237240320) (by decide) (join_sr (m := 290160640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 290160640) (by decide) (join_su (m := 237895680) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_su (m := 237895680) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (91/320 : ℝ) →
    rho ∈ Set.Icc (43/128 : ℝ) (447/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e2 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  have e3 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

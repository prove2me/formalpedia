-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_238551040_r198246400_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:51:44.539391+00:00
-- url     : https://prove2.me/submissions/2e9ce101-cf79-49c5-917e-27dccd9d8597

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 91/320]`, `ρ ∈ [121/512, 311/1280]` by 15 cells of the computing
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
theorem cell0 : cellOK 235929600 236584960 198246400 199639040 ⟨⟨63961523481, 63961523488⟩, ⟨62476030074, 65455893802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 235929600 236584960 199639040 201031680 ⟨⟨64394006246, 64394006253⟩, ⟨62906759701, 65890134934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 236584960 237240320 198246400 199639040 ⟨⟨63675005951, 63675005956⟩, ⟨62192627178, 65166233096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 236584960 237240320 199639040 201031680 ⟨⟨64105678957, 64105678962⟩, ⟨62621551305, 65598660244⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235929600 236584960 201031680 203816960 ⟨⟨65042377253, 65042377258⟩, ⟨63298402344, 66798985092⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 236584960 237240320 201031680 202424320 ⟨⟨64536165886, 64536165893⟩, ⟨63050289786, 66030900875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 236584960 237240320 202424320 203816960 ⟨⟨64966467189, 64966467195⟩, ⟨63478843067, 66462955440⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 237240320 237895680 198246400 199639040 ⟨⟨63389236037, 63389236040⟩, ⟨61909957254, 64877334829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 237240320 237895680 199639040 201031680 ⟨⟨63818102421, 63818102424⟩, ⟨62337079016, 65307951131⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 237895680 238551040 198246400 199639040 ⟨⟨63104208320, 63104208327⟩, ⟨61628014990, 64589193479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 237895680 238551040 199639040 201031680 ⟨⟨63531271202, 63531271209⟩, ⟨62053337506, 65018002056⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 237240320 237895680 201031680 202424320 ⟨⟨64246785049, 64246785051⟩, ⟨62764017437, 65738383251⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 237240320 237895680 202424320 203816960 ⟨⟨64675284360, 64675284363⟩, ⟨63190772956, 66168631632⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 237895680 238551040 201031680 202424320 ⟨⟨63958152624, 63958152630⟩, ⟨62478478962, 65446628763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 237895680 238551040 202424320 203816960 ⟨⟨64384853019, 64384853026⟩, ⟨62903439789, 65875074035⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 238551040 198246400 203816960 t = true :=
  ⟨_, (join_su (m := 237240320) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 236584960) (by decide) (join_sr (m := 199639040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 199639040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 236584960) (by decide) (leaf_ok cell4) (join_sr (m := 202424320) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 201031680) (by decide) (join_su (m := 237895680) (by decide) (join_sr (m := 199639040) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 199639040) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 237895680) (by decide) (join_sr (m := 202424320) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 202424320) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (91/320 : ℝ) →
    rho ∈ Set.Icc (121/512 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e2 : (((198246400 : ℤ) : ℝ) / (D : ℝ)) = (121/512 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

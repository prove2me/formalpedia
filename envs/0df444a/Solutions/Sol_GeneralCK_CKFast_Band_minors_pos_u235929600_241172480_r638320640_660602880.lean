-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_241172480_r638320640_660602880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:49:49.919992+00:00
-- url     : https://prove2.me/submissions/cd20b7c9-6fee-4228-bf41-feca962665f0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 23/80]`, `ρ ∈ [487/640, 63/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 237240320 638320640 643891200 ⟨⟨193505302037, 193505302046⟩, ⟨188895700469, 198168136439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 237240320 238551040 638320640 643891200 ⟨⟨191959835467, 191959835476⟩, ⟨187371282633, 196601447515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 235929600 237240320 643891200 649461760 ⟨⟨195068759410, 195068759419⟩, ⟨190445137801, 199745607984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237240320 238551040 643891200 649461760 ⟨⟨193512603938, 193512603947⟩, ⟨188910049391, 198168215236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 238551040 239861760 638320640 643891200 ⟨⟨190418148981, 190418148986⟩, ⟨185850547670, 195038635733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 239861760 241172480 638320640 643891200 ⟨⟨188880200653, 188880200661⟩, ⟨184333454436, 193479658411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 238551040 239861760 643891200 649461760 ⟨⟨191960213478, 191960213483⟩, ⟨187378629945, 196594683339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 239861760 241172480 643891200 649461760 ⟨⟨190411546374, 190411546382⟩, ⟨185850838565, 195024969900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 237240320 649461760 655032320 ⟨⟨196630989323, 196630989332⟩, ⟨191993353766, 201321844844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 237240320 238551040 649461760 655032320 ⟨⟨195064171025, 195064171034⟩, ⟨190447620367, 199733774859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 235929600 237240320 655032320 660602880 ⟨⟨198192009004, 198192009013⟩, ⟨193540365422, 202896864416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 237240320 238551040 655032320 660602880 ⟨⟨196614553551, 196614553559⟩, ⟨191984012215, 201298143367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 238551040 239861760 649461760 655032320 ⟨⟨193501102306, 193501102311⟩, ⟨188905541663, 198149549065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239861760 241172480 649461760 655032320 ⟨⟨191941741778, 191941741787⟩, ⟨187367077012, 196569125360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 238551040 239861760 655032320 660602880 ⟨⟨195040831887, 195040831889⟩, ⟨190431299089, 199703249488⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239861760 241172480 655032320 660602880 ⟨⟨193470802897, 193470802905⟩, ⟨188882185655, 198112140969⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 241172480 638320640 660602880 t = true :=
  ⟨_, (join_sr (m := 649461760) (by decide) (join_su (m := 238551040) (by decide) (join_sr (m := 643891200) (by decide) (join_su (m := 237240320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 237240320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 643891200) (by decide) (join_su (m := 239861760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 239861760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 238551040) (by decide) (join_sr (m := 655032320) (by decide) (join_su (m := 237240320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 237240320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 655032320) (by decide) (join_su (m := 239861760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 239861760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (487/640 : ℝ) (63/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((638320640 : ℤ) : ℝ) / (D : ℝ)) = (487/640 : ℝ) := by norm_num [D]
  have e3 : (((660602880 : ℤ) : ℝ) / (D : ℝ)) = (63/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_222822400_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:44:14.140697+00:00
-- url     : https://prove2.me/submissions/01df4db2-2d1f-450d-acba-22b6760adc42

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 17/64]`, `ρ ∈ [277/1280, 147/640]` by 18 cells of the computing
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
theorem cell0 : cellOK 220200960 220856320 181534720 184320000 ⟨⟨65574368419, 65574368425⟩, ⟨63746791786, 67415790827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220856320 221511680 181534720 184320000 ⟨⟨65290119624, 65290119627⟩, ⟨63467383994, 67126643644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 220200960 220856320 184320000 187105280 ⟨⟨66533813787, 66533813793⟩, ⟨64702174289, 68379305297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 220856320 221511680 184320000 187105280 ⟨⟨66245717500, 66245717503⟩, ⟨64418929882, 68086299910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 221511680 222167040 181534720 182927360 ⟨⟨64768621044, 64768621050⟩, ⟨63232907844, 66313834236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 221511680 222167040 182927360 184320000 ⟨⟨65244754154, 65244754160⟩, ⟨63707183635, 66791829171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222167040 222822400 181534720 182927360 ⟨⟨64487022917, 64487022923⟩, ⟨62954722166, 66028790232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222167040 222822400 182927360 184320000 ⟨⟨64961237024, 64961237031⟩, ⟨63427083475, 66504861688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 221511680 222167040 184320000 187105280 ⟨⟨65958477582, 65958477589⟩, ⟨64136518801, 67794174322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 222167040 222822400 184320000 187105280 ⟨⟨65672087632, 65672087638⟩, ⟨63854934816, 67502921944⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 220200960 220856320 187105280 189890560 ⟨⟨67492222171, 67492222176⟩, ⟨65656524981, 69341777528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 220856320 221511680 187105280 189890560 ⟨⟨67200290705, 67200290708⟩, ⟨65369456167, 69044926359⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 220200960 220856320 189890560 192675840 ⟨⟨68449598952, 68449598958⟩, ⟨66609849219, 70303212935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 220856320 221511680 189890560 192675840 ⟨⟨68153844542, 68153844544⟩, ⟨66318968121, 70002528325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 221511680 222167040 187105280 189890560 ⟨⟨66909223284, 66909223291⟩, ⟨65083228350, 68748962665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 222167040 222822400 187105280 189890560 ⟨⟨66619013463, 66619013470⟩, ⟨64797835258, 68453879812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 221511680 222167040 189890560 192675840 ⟨⟨67858961730, 67858961736⟩, ⟨66028935574, 69702738742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 222167040 222822400 189890560 192675840 ⟨⟨67564944030, 67564944035⟩, ⟨65739745262, 69403837513⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 222822400 181534720 192675840 t = true :=
  ⟨_, (join_sr (m := 187105280) (by decide) (join_su (m := 221511680) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 220856320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 220856320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184320000) (by decide) (join_su (m := 222167040) (by decide) (join_sr (m := 182927360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 182927360) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 222167040) (by decide) (leaf_ok cell8) (leaf_ok cell9)))) (join_su (m := 221511680) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 220856320) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_su (m := 220856320) (by decide) (leaf_ok cell12) (leaf_ok cell13))) (join_sr (m := 189890560) (by decide) (join_su (m := 222167040) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_su (m := 222167040) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (17/64 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

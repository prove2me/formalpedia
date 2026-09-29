-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_33554432_r547880960_644874240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:33:46.030471+00:00
-- url     : https://prove2.me/submissions/9e33657c-337c-48c0-b0f3-1fd53619cf71

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 1/25]`, `ρ ∈ [209/320, 123/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 16777216 20971520 547880960 572129280 ⟨⟨533430582855, 533430582873⟩, ⟨492036510198, 575426621893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 20971520 25165824 547880960 572129280 ⟨⟨520188084327, 520188084344⟩, ⟨479993807454, 561089900205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 16777216 20971520 572129280 596377600 ⟨⟨544815307436, 544815307453⟩, ⟨504058956054, 586032294840⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 20971520 25165824 572129280 596377600 ⟨⟨531715592078, 531715592095⟩, ⟨492088698912, 571914039905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 25165824 29360128 547880960 572129280 ⟨⟨507652031796, 507652031813⟩, ⟨468551522374, 547536591722⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 29360128 33554432 547880960 572129280 ⟨⟨495719800033, 495719800048⟩, ⟨457632622088, 534648772442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 25165824 29360128 572129280 596377600 ⟨⟨519294060343, 519294060359⟩, ⟨480697237237, 558544414769⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 29360128 33554432 572129280 596377600 ⟨⟨507451868470, 507451868489⟩, ⟨469810296150, 545810203538⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 16777216 20971520 596377600 620625920 ⟨⟨556043989251, 556043989271⟩, ⟨515888367504, 596530179221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 20971520 25165824 596377600 620625920 ⟨⟨543079050749, 543079050766⟩, ⟨503987998277, 582616013688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 16777216 20971520 620625920 644874240 ⟨⟨567134629953, 567134629969⟩, ⟨527545741678, 606933753357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 20971520 25165824 620625920 644874240 ⟨⟨554296927061, 554296927081⟩, ⟨515712547762, 593210550036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 25165824 29360128 596377600 620625920 ⟨⟨530766100619, 530766100636⟩, ⟨492646162567, 569418519065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 29360128 33554432 596377600 620625920 ⟨⟨519009729957, 519009729974⟩, ⟨481791107079, 556828731615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 25165824 29360128 620625920 644874240 ⟨⟨542086854499, 542086854515⟩, ⟨504418857156, 580174536747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 29360128 33554432 620625920 644874240 ⟨⟨530412138715, 530412138731⟩, ⟨493595231220, 567720611755⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 33554432 547880960 644874240 t = true :=
  ⟨_, (join_sr (m := 596377600) (by decide) (join_su (m := 25165824) (by decide) (join_sr (m := 572129280) (by decide) (join_su (m := 20971520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 20971520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 572129280) (by decide) (join_su (m := 29360128) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 29360128) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 25165824) (by decide) (join_sr (m := 620625920) (by decide) (join_su (m := 20971520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 20971520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 620625920) (by decide) (join_su (m := 29360128) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 29360128) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (209/320 : ℝ) (123/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((547880960 : ℤ) : ℝ) / (D : ℝ)) = (209/320 : ℝ) := by norm_num [D]
  have e3 : (((644874240 : ℤ) : ℝ) / (D : ℝ)) = (123/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

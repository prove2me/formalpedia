-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_138936320_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:08:03.263766+00:00
-- url     : https://prove2.me/submissions/60c3bc71-43a2-4509-a9c0-bcfae7f88912

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 53/320]`, `ρ ∈ [137/1280, 73/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 136970240 89784320 91258880 ⟨⟨58628381713, 58628381720⟩, ⟨56570923429, 60704233827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136314880 136970240 91258880 92733440 ⟨⟨59527711160, 59527711168⟩, ⟨57467130014, 61606672591⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 136970240 137625600 89784320 91258880 ⟨⟨58354861841, 58354861847⟩, ⟨56304857246, 60423137562⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 136970240 137625600 91258880 92733440 ⟨⟨59250431857, 59250431865⟩, ⟨57197314243, 61321807450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 136314880 136970240 92733440 94208000 ⟨⟨60425442180, 60425442187⟩, ⟨58361750441, 62507500593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 136314880 136970240 94208000 95682560 ⟨⟨61321582700, 61321582707⟩, ⟨59254792552, 63406725845⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 136970240 137625600 92733440 94208000 ⟨⟨60144422400, 60144422408⟩, ⟨58088203847, 62218885716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 136970240 137625600 94208000 95682560 ⟨⟨61036841260, 61036841268⟩, ⟨58977533766, 63114380234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 137625600 138280960 89784320 91258880 ⟨⟨58083078351, 58083078357⟩, ⟨56040465084, 60143841440⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 137625600 138280960 91258880 92733440 ⟨⟨58974907725, 58974907732⟩, ⟨56929191275, 61038761232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 138280960 138936320 89784320 91258880 ⟨⟨57813011305, 57813011311⟩, ⟨55777727796, 59866324700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 138280960 138936320 91258880 92733440 ⟨⟨58701118649, 58701118656⟩, ⟨56662741789, 60757513012⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 137625600 138280960 92733440 94208000 ⟨⟨59865176337, 59865176345⟩, ⟨57816368598, 61932108301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 137625600 138280960 94208000 95682560 ⟨⟨60753891845, 60753891853⟩, ⟨58702004633, 62823890389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 138280960 138936320 92733440 94208000 ⟨⟨59587683712, 59587683718⟩, ⟨57546225210, 61647147264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 138280960 138936320 94208000 95682560 ⟨⟨60472714018, 60472714024⟩, ⟨58428185509, 62535235060⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 138936320 89784320 95682560 t = true :=
  ⟨_, (join_su (m := 137625600) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 136970240) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 91258880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 136970240) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 94208000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 92733440) (by decide) (join_su (m := 138280960) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 91258880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 138280960) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 94208000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (53/320 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((138936320 : ℤ) : ℝ) / (D : ℝ)) = (53/320 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

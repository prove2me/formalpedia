-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_247726080_r164823040_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:26:46.173556+00:00
-- url     : https://prove2.me/submissions/f30a4b74-53b2-4188-979a-af223ebb8852

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 189/640]`, `ρ ∈ [503/2560, 13/64]` by 15 cells of the computing
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
theorem cell0 : cellOK 246415360 246743040 164823040 166215680 ⟨⟨49781697666, 49781697668⟩, ⟨48965957283, 50600377456⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246743040 247070720 164823040 166215680 ⟨⟨49665403059, 49665403065⟩, ⟨48850661384, 50483078503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246415360 246743040 166215680 167608320 ⟨⟨50189839569, 50189839570⟩, ⟨49373186379, 51009433594⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 246743040 247070720 166215680 167608320 ⟨⟨50072638571, 50072638577⟩, ⟨49256985451, 50891226892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 247070720 247398400 164823040 166215680 ⟨⟨49549256924, 49549256931⟩, ⟨48735511808, 50365930185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 247398400 247726080 164823040 166215680 ⟨⟨49433258714, 49433258720⟩, ⟨48620508015, 50248931950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247070720 247398400 166215680 167608320 ⟨⟨49955586896, 49955586903⟩, ⟨49140931698, 50773171678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247398400 247726080 166215680 167608320 ⟨⟨49838683993, 49838684000⟩, ⟨49025024573, 50655267394⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 246415360 246743040 167608320 169000960 ⟨⟨50597818623, 50597818626⟩, ⟨49780252857, 51418326650⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 246743040 247070720 167608320 169000960 ⟨⟨50479712306, 50479712311⟩, ⟨49663147970, 51299213274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 246415360 247070720 169000960 170393600 ⟨⟨50946111003, 50946111008⟩, ⟨49544194220, 52356346647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 247070720 247398400 167608320 169000960 ⟨⟨50361756155, 50361756161⟩, ⟨49546191099, 51180252229⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 247398400 247726080 167608320 169000960 ⟨⟨50243949618, 50243949625⟩, ⟨49429381697, 51061442961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 247070720 247398400 169000960 170393600 ⟨⟨50767765066, 50767765071⟩, ⟨49951290376, 51587172207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 247398400 247726080 169000960 170393600 ⟨⟨50649055953, 50649055958⟩, ⟨49833579751, 51467459013⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 247726080 164823040 170393600 t = true :=
  ⟨_, (join_sr (m := 167608320) (by decide) (join_su (m := 247070720) (by decide) (join_sr (m := 166215680) (by decide) (join_su (m := 246743040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 246743040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 166215680) (by decide) (join_su (m := 247398400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 247398400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 247070720) (by decide) (join_sr (m := 169000960) (by decide) (join_su (m := 246743040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 169000960) (by decide) (join_su (m := 247398400) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 247398400) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (189/640 : ℝ) →
    rho ∈ Set.Icc (503/2560 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((247726080 : ℤ) : ℝ) / (D : ℝ)) = (189/640 : ℝ) := by norm_num [D]
  have e2 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

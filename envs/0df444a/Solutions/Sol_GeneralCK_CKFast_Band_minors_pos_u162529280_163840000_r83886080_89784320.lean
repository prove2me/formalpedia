-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_163840000_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:17:54.63578+00:00
-- url     : https://prove2.me/submissions/19a39ed2-4b04-48e0-b9af-7c2639442584

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 25/128]`, `ρ ∈ [1/10, 137/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 162529280 162856960 83886080 85360640 ⟨⟨45862264547, 45862264555⟩, ⟨44743967372, 46986247932⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 162856960 163184640 83886080 85360640 ⟨⟨45759765615, 45759765618⟩, ⟨44643382181, 46881817541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 162529280 162856960 85360640 86835200 ⟨⟨46629173829, 46629173837⟩, ⟨45509296072, 47754735021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 162856960 163184640 85360640 86835200 ⟨⟨46525085976, 46525085979⟩, ⟨45407124881, 47648712835⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 163184640 163512320 83886080 85360640 ⟨⟨45657537268, 45657537275⟩, ⟨44543060973, 46777664437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 163512320 163840000 83886080 85360640 ⟨⟨45555578144, 45555578151⟩, ⟨44443002419, 46673787206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 163184640 163512320 85360640 86835200 ⟨⟨46421272186, 46421272193⟩, ⟨45305221145, 47542971414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 163512320 163840000 85360640 86835200 ⟨⟨46317731079, 46317731085⟩, ⟨45203583520, 47437509332⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 162529280 162856960 86835200 88309760 ⟨⟨47395067246, 47395067253⟩, ⟨46273613433, 48522201705⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 162856960 163184640 86835200 88309760 ⟨⟨47289396464, 47289396467⟩, ⟨46169862199, 48414593748⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 162529280 162856960 88309760 89784320 ⟨⟨48159948919, 48159948926⟩, ⟨47036923553, 49288652126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 162856960 163184640 88309760 89784320 ⟨⟨48052701165, 48052701168⟩, ⟨46931598196, 49179464392⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 163184640 163512320 86835200 88309760 ⟨⟨47184003186, 47184003192⟩, ⟨46066381855, 48307270003⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 163512320 163840000 86835200 88309760 ⟨⟨47078886015, 47078886021⟩, ⟨45963171043, 48200229026⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 163184640 163512320 88309760 89784320 ⟨⟨47945734318, 47945734326⟩, ⟨46826547130, 49070564279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 163512320 163840000 88309760 89784320 ⟨⟨47839046973, 47839046979⟩, ⟨46721768982, 48961950328⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 163840000 83886080 89784320 t = true :=
  ⟨_, (join_sr (m := 86835200) (by decide) (join_su (m := 163184640) (by decide) (join_sr (m := 85360640) (by decide) (join_su (m := 162856960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 162856960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 85360640) (by decide) (join_su (m := 163512320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 163512320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 163184640) (by decide) (join_sr (m := 88309760) (by decide) (join_su (m := 162856960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 162856960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 88309760) (by decide) (join_su (m := 163512320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 163512320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (25/128 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((163840000 : ℤ) : ℝ) / (D : ℝ)) = (25/128 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

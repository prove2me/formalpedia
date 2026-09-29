-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u112721920_115343360_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:05:34.007705+00:00
-- url     : https://prove2.me/submissions/98db55c7-05cb-43f2-9793-9b7c7038bde7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/320, 11/80]`, `ρ ∈ [1/10, 137/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 112721920 113377280 83886080 85360640 ⟨⟨65609309756, 65609309760⟩, ⟨63248035464, 67994687393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 112721920 113377280 85360640 86835200 ⟨⟨66668142386, 66668142389⟩, ⟨64303314194, 69057039380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 113377280 114032640 83886080 85360640 ⟨⟨65275403141, 65275403149⟩, ⟨62924461116, 67650253247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 113377280 114032640 85360640 86835200 ⟨⟨66329544590, 66329544597⟩, ⟨63975058774, 68707904783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 112721920 113377280 86835200 88309760 ⟨⟨67724437798, 67724437802⟩, ⟨65356077897, 70116831893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 112721920 113377280 88309760 89784320 ⟨⟨68778211610, 68778211614⟩, ⟨66406341983, 71174080757⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 113377280 114032640 86835200 88309760 ⟨⟨67381180509, 67381180518⟩, ⟨65023172747, 69763028884⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 113377280 114032640 88309760 89784320 ⟨⟨68430326231, 68430326238⟩, ⟨66068818163, 70815641076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 114032640 114688000 83886080 85360640 ⟨⟨64944108773, 64944108782⟩, ⟨62603395629, 67308537371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 114032640 114688000 85360640 86835200 ⟨⟨65993587110, 65993587118⟩, ⟨63649340346, 68361516449⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 114688000 115343360 83886080 85360640 ⟨⟨64615391289, 64615391296⟩, ⟨62284805210, 66969502787⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 114688000 115343360 85360640 86835200 ⟨⟨65660234301, 65660234310⟩, ⟨63326124830, 68017837119⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 114032640 114688000 86835200 88309760 ⟨⟨67040591165, 67040591172⟩, ⟨64692832282, 69411999678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 114032640 114688000 88309760 89784320 ⟨⟨68085135981, 68085135989⟩, ⟨65733886284, 70460002297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 114688000 115343360 86835200 88309760 ⟨⟨66702633841, 66702633850⟩, ⟨64365022144, 69063706746⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 114688000 115343360 88309760 89784320 ⟨⟨67742604673, 67742604682⟩, ⟨65401511721, 70107126625⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 112721920 115343360 83886080 89784320 t = true :=
  ⟨_, (join_su (m := 114032640) (by decide) (join_sr (m := 86835200) (by decide) (join_su (m := 113377280) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 85360640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 113377280) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 88309760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 86835200) (by decide) (join_su (m := 114688000) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 85360640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 114688000) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 88309760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/320 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((112721920 : ℤ) : ℝ) / (D : ℝ)) = (43/320 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

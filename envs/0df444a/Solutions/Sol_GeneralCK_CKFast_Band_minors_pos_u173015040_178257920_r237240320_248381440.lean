-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u173015040_178257920_r237240320_248381440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:18:34.087815+00:00
-- url     : https://prove2.me/submissions/1af4d4ce-4779-4114-be72-a8ed2407030a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/160, 17/80]`, `ρ ∈ [181/640, 379/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 173015040 174325760 237240320 240025600 ⟨⟨113312588438, 113312588443⟩, ⟨109463868783, 117211903500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 173015040 174325760 240025600 242810880 ⟨⟨114526767122, 114526767128⟩, ⟨110669817731, 118434288236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 174325760 175636480 237240320 240025600 ⟨⟨112410195860, 112410195868⟩, ⟨108582441853, 116288134313⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 174325760 175636480 240025600 242810880 ⟨⟨113616232857, 113616232864⟩, ⟨109780267742, 117502361085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 173015040 174325760 242810880 245596160 ⟨⟨115738916875, 115738916880⟩, ⟨111873760114, 119654621239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 173015040 174325760 245596160 248381440 ⟨⟨116949051214, 116949051216⟩, ⟨113075709273, 120872916206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 174325760 175636480 242810880 245596160 ⟨⟨114820282126, 114820282135⟩, ⟨110976127659, 118714577948⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 174325760 175636480 245596160 248381440 ⟨⟨116022356818, 116022356825⟩, ⟨112170034581, 119924798221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 175636480 176947200 237240320 240025600 ⟨⟨111514502535, 111514502543⟩, ⟨107707471214, 115371313305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 175636480 176947200 240025600 242810880 ⟨⟨112712426392, 112712426401⟩, ⟨108897203199, 116577409992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 176947200 178257920 237240320 240025600 ⟨⟨110625401690, 110625401698⟩, ⟨106838854325, 114461329358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 176947200 178257920 240025600 242810880 ⟨⟨111815240819, 111815240828⟩, ⟨108020521398, 115659323727⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 175636480 176947200 242810880 245596160 ⟨⟨113908403000, 113908403008⟩, ⟨110085009085, 117781537853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 175636480 176947200 245596160 248381440 ⟨⟨115102445145, 115102445151⟩, ⟨111270901493, 118983709841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 176947200 178257920 242810880 245596160 ⟨⟨113003172457, 113003172466⟩, ⟨109200301535, 116855389625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 176947200 178257920 245596160 248381440 ⟨⟨114189209037, 114189209044⟩, ⟨110378207018, 118049539643⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 173015040 178257920 237240320 248381440 t = true :=
  ⟨_, (join_su (m := 175636480) (by decide) (join_sr (m := 242810880) (by decide) (join_su (m := 174325760) (by decide) (join_sr (m := 240025600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 240025600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 174325760) (by decide) (join_sr (m := 245596160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 245596160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 242810880) (by decide) (join_su (m := 176947200) (by decide) (join_sr (m := 240025600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 240025600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 176947200) (by decide) (join_sr (m := 245596160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 245596160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/160 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (181/640 : ℝ) (379/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e3 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u149422080_152043520_r154664960_166461440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:39:33.731847+00:00
-- url     : https://prove2.me/submissions/6c55a59e-7c62-4a68-84e3-64554facca08

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [57/320, 29/160]`, `ρ ∈ [59/320, 127/640]` by 12 cells of the computing
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
theorem cell0 : cellOK 149422080 150077440 154664960 157614080 ⟨⟨89143830636, 89143830643⟩, ⟨86598899935, 91713600193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 150077440 150732800 154664960 157614080 ⟨⟨88762764234, 88762764242⟩, ⟨86227014807, 91323203762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 149422080 150077440 157614080 160563200 ⟨⟨90695694087, 90695694094⟩, ⟨88145001807, 93271180858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 150077440 150732800 157614080 160563200 ⟨⟨90308962461, 90308962469⟩, ⟨87767461209, 92875110458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 150732800 151388160 154664960 157614080 ⟨⟨88383634964, 88383634970⟩, ⟨85857002488, 90934810195⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 151388160 152043520 154664960 157614080 ⟨⟨88006423944, 88006423953⟩, ⟨85488844798, 90548399891⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 150732800 151388160 157614080 160563200 ⟨⟨89924186240, 89924186248⟩, ⟨87391811826, 92481061039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 151388160 152043520 157614080 160563200 ⟨⟨89541346440, 89541346447⟩, ⟨87018035379, 92089012903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 149422080 150732800 160563200 163512320 ⟨⟨92046997046, 92046997054⟩, ⟨87965476656, 96191477499⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 149422080 150732800 163512320 166461440 ⟨⟨93587832034, 93587832041⟩, ⟨89496126050, 97742423744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 150732800 152043520 160563200 163512320 ⟨⟨91266234110, 91266234118⟩, ⟨87211015651, 95383737496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 150732800 152043520 163512320 166461440 ⟨⟨92795950478, 92795950487⟩, ⟨88730579477, 96923536452⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 149422080 152043520 154664960 166461440 t = true :=
  ⟨_, (join_sr (m := 160563200) (by decide) (join_su (m := 150732800) (by decide) (join_sr (m := 157614080) (by decide) (join_su (m := 150077440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 150077440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 157614080) (by decide) (join_su (m := 151388160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 151388160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 150732800) (by decide) (join_sr (m := 163512320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 163512320) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (57/320 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (59/320 : ℝ) (127/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((149422080 : ℤ) : ℝ) / (D : ℝ)) = (57/320 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e3 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

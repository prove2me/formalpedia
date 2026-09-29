-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_120586240_r201850880_225443840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:34:58.924538+00:00
-- url     : https://prove2.me/submissions/e15babe4-2fd9-4dd2-a2ba-e3f5b4c49dc1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 23/160]`, `ρ ∈ [77/320, 43/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 115343360 116654080 201850880 207749120 ⟨⟨141932060377, 141932060387⟩, ⟨135533996166, 148461517659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 116654080 117964800 201850880 207749120 ⟨⟨140703842221, 140703842232⟩, ⟨134359385111, 147177977866⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 115343360 116654080 207749120 213647360 ⟨⟨145448236405, 145448236416⟩, ⟨139030398407, 151996458021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 116654080 117964800 207749120 213647360 ⟨⟨144197736507, 144197736515⟩, ⟨137833372350, 150690805942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 117964800 119275520 201850880 207749120 ⟨⟨139490088864, 139490088874⟩, ⟨133198378235, 145909798369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 119275520 120586240 201850880 207749120 ⟨⟨138290489651, 138290489661⟩, ⟨132050685873, 144656646569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 117964800 119275520 207749120 213647360 ⟨⟨142961791914, 142961791923⟩, ⟨136650051023, 149400593392⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 119275520 120586240 207749120 213647360 ⟨⟨141740092762, 141740092773⟩, ⟨135480145109, 148125489050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 115343360 116654080 213647360 219545600 ⟨⟨148940447586, 148940447596⟩, ⟨142503258372, 155507014739⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 116654080 117964800 213647360 219545600 ⟨⟨147668137479, 147668137489⟩, ⟨141284280369, 154179729927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 115343360 116654080 219545600 225443840 ⟨⟨152409186388, 152409186396⟩, ⟨145953054947, 158993693967⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 116654080 117964800 219545600 225443840 ⟨⟨151115523395, 151115523405⟩, ⟨144712574302, 157645241297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 117964800 119275520 213647360 219545600 ⟨⟨146410464198, 146410464206⟩, ⟨140079098740, 152867954831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 119275520 120586240 213647360 219545600 ⟨⟨145167118837, 145167118846⟩, ⟨138887424699, 151571359569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 117964800 119275520 219545600 225443840 ⟨⟨149836570182, 149836570191⟩, ⟨143485973189, 156312359917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 119275520 120586240 219545600 225443840 ⟨⟨148572018964, 148572018975⟩, ⟨142272963508, 154994721545⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 120586240 201850880 225443840 t = true :=
  ⟨_, (join_sr (m := 213647360) (by decide) (join_su (m := 117964800) (by decide) (join_sr (m := 207749120) (by decide) (join_su (m := 116654080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 116654080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 207749120) (by decide) (join_su (m := 119275520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 119275520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 117964800) (by decide) (join_sr (m := 219545600) (by decide) (join_su (m := 116654080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 116654080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 219545600) (by decide) (join_su (m := 119275520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 119275520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (23/160 : ℝ) →
    rho ∈ Set.Icc (77/320 : ℝ) (43/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e2 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e3 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_247726080_r159252480_164823040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:26:45.776011+00:00
-- url     : https://prove2.me/submissions/759104dd-3402-466f-a01b-6529207acf03

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 189/640]`, `ρ ∈ [243/1280, 503/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 246743040 159252480 160645120 ⟨⟨48147494136, 48147494137⟩, ⟨47335407324, 48962514610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246743040 247070720 159252480 160645120 ⟨⟨48034835856, 48034835861⟩, ⟨47223742254, 48848857460⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246415360 246743040 160645120 162037760 ⟨⟨48556291152, 48556291154⟩, ⟨47743290595, 49372226812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 246743040 247070720 160645120 162037760 ⟨⟨48442722169, 48442722175⟩, ⟨47630716204, 49257657584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 247070720 247398400 159252480 160645120 ⟨⟨47922322590, 47922322595⟩, ⟨47112220057, 48735347482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 247398400 247726080 159252480 160645120 ⟨⟨47809953802, 47809953807⟩, ⟨47000840200, 48621984136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247070720 247398400 160645120 162037760 ⟨⟨48329299074, 48329299079⟩, ⟨47518285555, 49143236402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247398400 247726080 160645120 162037760 ⟨⟨48216021327, 48216021332⟩, ⟨47405998117, 49028962724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 246415360 246743040 162037760 163430400 ⟨⟨48964923830, 48964923833⟩, ⟨48151009764, 49781774437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 246743040 247070720 162037760 163430400 ⟨⟨48850445228, 48850445233⟩, ⟨48037527128, 49666294218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 246415360 246743040 163430400 164823040 ⟨⟨49373392544, 49373392546⟩, ⟨48558565203, 50191157861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 246743040 247070720 163430400 164823040 ⟨⟨49258005401, 49258005407⟩, ⟨48444175399, 50074767735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 247070720 247398400 162037760 163430400 ⟨⟨48736113380, 48736113385⟩, ⟨47924189102, 49550962913⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 247398400 247726080 162037760 163430400 ⟨⟨48621927744, 48621927749⟩, ⟨47810995149, 49435779978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 247070720 247398400 163430400 164823040 ⟨⟨49142765875, 49142765880⟩, ⟨48329931066, 49958527385⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 247398400 247726080 163430400 164823040 ⟨⟨49027673419, 49027673424⟩, ⟨48215831661, 49842436266⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 247726080 159252480 164823040 t = true :=
  ⟨_, (join_sr (m := 162037760) (by decide) (join_su (m := 247070720) (by decide) (join_sr (m := 160645120) (by decide) (join_su (m := 246743040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 246743040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 160645120) (by decide) (join_su (m := 247398400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 247398400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 247070720) (by decide) (join_sr (m := 163430400) (by decide) (join_su (m := 246743040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 246743040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 163430400) (by decide) (join_su (m := 247398400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 247398400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (189/640 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (503/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((247726080 : ℤ) : ℝ) / (D : ℝ)) = (189/640 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

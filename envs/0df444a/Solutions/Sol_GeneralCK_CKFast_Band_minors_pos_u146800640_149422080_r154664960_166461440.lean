-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_149422080_r154664960_166461440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:39:29.056612+00:00
-- url     : https://prove2.me/submissions/ceb12a46-0071-46cc-9568-ec53749ee5e9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 57/320]`, `ρ ∈ [59/320, 127/640]` by 11 cells of the computing
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
theorem cell0 : cellOK 146800640 147456000 154664960 157614080 ⟨⟨90687853842, 90687853849⟩, ⟨88105540416, 93295615590⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 147456000 148111360 154664960 157614080 ⟨⟨90298845138, 90298845147⟩, ⟨87725977504, 92897006521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 146800640 148111360 157614080 160563200 ⟨⟨92064933471, 92064933474⟩, ⟨87939961028, 96254337906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 148111360 148766720 154664960 157614080 ⟨⟨89911851586, 89911851593⟩, ⟨87348362508, 92500481324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 148766720 149422080 154664960 157614080 ⟨⟨89526853296, 89526853301⟩, ⟨86972676284, 92106019341⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 148111360 148766720 157614080 160563200 ⟨⟨91475100715, 91475100722⟩, ⟨88905830987, 94069464677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 148766720 149422080 157614080 160563200 ⟨⟨91084400346, 91084400351⟩, ⟨88524452147, 93669292192⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 146800640 148111360 160563200 163512320 ⟨⟨93632474384, 93632474387⟩, ⟨89497195529, 97832102369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 146800640 148111360 163512320 166461440 ⟨⟨95195756045, 95195756048⟩, ⟨91050227937, 99405549735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 148111360 149422080 160563200 163512320 ⟨⟨92835691590, 92835691599⟩, ⟨88727487225, 97007543977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 148111360 149422080 163512320 166461440 ⟨⟨94387714762, 94387714769⟩, ⟨90269292549, 98569706129⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 149422080 154664960 166461440 t = true :=
  ⟨_, (join_sr (m := 160563200) (by decide) (join_su (m := 148111360) (by decide) (join_sr (m := 157614080) (by decide) (join_su (m := 147456000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 157614080) (by decide) (join_su (m := 148766720) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (join_su (m := 148766720) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_su (m := 148111360) (by decide) (join_sr (m := 163512320) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 163512320) (by decide) (leaf_ok cell9) (leaf_ok cell10))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (57/320 : ℝ) →
    rho ∈ Set.Icc (59/320 : ℝ) (127/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((149422080 : ℤ) : ℝ) / (D : ℝ)) = (57/320 : ℝ) := by norm_num [D]
  have e2 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e3 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

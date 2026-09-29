-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_138936320_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:28:15.425377+00:00
-- url     : https://prove2.me/submissions/5801dd55-7aa5-499e-aacc-6b98317a4056

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 53/320]`, `ρ ∈ [109/640, 59/320]` by 12 cells of the computing
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
theorem cell0 : cellOK 136314880 136970240 142868480 145817600 ⟨⟨90474365441, 90474365450⟩, ⟨87755293366, 93221850869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136970240 137625600 142868480 145817600 ⟨⟨90074958409, 90074958418⟩, ⟨87366488448, 92811654774⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 136314880 136970240 145817600 148766720 ⟨⟨92164560692, 92164560700⟩, ⟨89439371422, 94918095277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 136970240 137625600 145817600 148766720 ⟨⟨91758872572, 91758872581⟩, ⟨89044293980, 94501610966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 137625600 138280960 142868480 145817600 ⟨⟨89677836059, 89677836067⟩, ⟨86979886516, 92403826998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 138280960 138936320 142868480 145817600 ⟨⟨89282974203, 89282974210⟩, ⟨86595464357, 91998342354⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 137625600 138280960 145817600 148766720 ⟨⟨91355492019, 91355492026⟩, ⟨88651442620, 94087517619⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 138280960 138936320 145817600 148766720 ⟨⟨90954394703, 90954394711⟩, ⟨88260793988, 93675789917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 136314880 137625600 148766720 151715840 ⟨⟨93643176036, 93643176044⟩, ⟨89318710450, 98038620302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 136314880 137625600 151715840 154664960 ⟨⟨95319672629, 95319672636⟩, ⟨90984454829, 99725744385⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 137625600 138936320 148766720 151715840 ⟨⟨92824007623, 92824007632⟩, ⟨88529968530, 97188180801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 137625600 138936320 151715840 154664960 ⟨⟨94488216664, 94488216671⟩, ⟨90183455533, 98862993357⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 138936320 142868480 154664960 t = true :=
  ⟨_, (join_sr (m := 148766720) (by decide) (join_su (m := 137625600) (by decide) (join_sr (m := 145817600) (by decide) (join_su (m := 136970240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 136970240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 145817600) (by decide) (join_su (m := 138280960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 138280960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 137625600) (by decide) (join_sr (m := 151715840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 151715840) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (53/320 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((138936320 : ℤ) : ℝ) / (D : ℝ)) = (53/320 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

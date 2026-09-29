-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_149422080_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:31:13.25251+00:00
-- url     : https://prove2.me/submissions/c4587eb1-060b-4a15-bdd8-203666e9c70c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 57/320]`, `ρ ∈ [109/640, 59/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 147456000 142868480 145817600 ⟨⟨84345063027, 84345063035⟩, ⟨81786340320, 86929426589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 147456000 148111360 142868480 145817600 ⟨⟨83979488297, 83979488306⟩, ⟨81430169423, 86554289133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 146800640 147456000 145817600 148766720 ⟨⟨85937430801, 85937430808⟩, ⟨83372750303, 88527704284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 147456000 148111360 145817600 148766720 ⟨⟨85565924900, 85565924909⟩, ⟨83010659543, 88146625432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 148111360 148766720 142868480 145817600 ⟨⟨83615848870, 83615848879⟩, ⟨81075866038, 86181156331⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 148766720 149422080 142868480 145817600 ⟨⟨83254125338, 83254125343⟩, ⟨80723411513, 85810007990⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 148111360 148766720 145817600 148766720 ⟨⟨85196375047, 85196375056⟩, ⟨82650457171, 87767571828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 148766720 149422080 145817600 148766720 ⟨⟨84828761705, 84828761710⟩, ⟨82292124400, 87390523157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 146800640 147456000 148766720 151715840 ⟨⟨87525326008, 87525326016⟩, ⟨84954728122, 90121468832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 147456000 148111360 148766720 151715840 ⟨⟨87147937791, 87147937798⟩, ⟨84586765801, 89734497987⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 146800640 147456000 151715840 154664960 ⟨⟨89108787533, 89108787540⟩, ⟨86532312167, 91710759616⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 147456000 148111360 151715840 154664960 ⟨⟨88725565248, 88725565255⟩, ⟨86158525990, 91317945567⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 148111360 148766720 148766720 151715840 ⟨⟨86772525837, 86772525844⟩, ⟨84220712219, 89349572452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 148766720 149422080 148766720 151715840 ⟨⟨86399070487, 86399070492⟩, ⟨83856548467, 88966671794⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 148111360 148766720 151715840 154664960 ⟨⟨88344338923, 88344338929⟩, ⟨85786668393, 90927196366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 148766720 149422080 151715840 154664960 ⟨⟨87965088784, 87965088786⟩, ⟨85416720346, 90538491466⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 149422080 142868480 154664960 t = true :=
  ⟨_, (join_sr (m := 148766720) (by decide) (join_su (m := 148111360) (by decide) (join_sr (m := 145817600) (by decide) (join_su (m := 147456000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 147456000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 145817600) (by decide) (join_su (m := 148766720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 148766720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 148111360) (by decide) (join_sr (m := 151715840) (by decide) (join_su (m := 147456000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 147456000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 151715840) (by decide) (join_su (m := 148766720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 148766720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (57/320 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((149422080 : ℤ) : ℝ) / (D : ℝ)) = (57/320 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

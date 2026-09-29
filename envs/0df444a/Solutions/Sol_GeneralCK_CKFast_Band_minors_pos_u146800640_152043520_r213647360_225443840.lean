-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_152043520_r213647360_225443840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:48:52.164154+00:00
-- url     : https://prove2.me/submissions/7f7f2488-22fa-4b11-9908-f33a4282449c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 29/160]`, `ρ ∈ [163/640, 43/160]` by 13 cells of the computing
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
theorem cell0 : cellOK 146800640 148111360 213647360 216596480 ⟨⟨121153886644, 121153886647⟩, ⟨116842267801, 125528254653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 146800640 148111360 216596480 219545600 ⟨⟨122646403018, 122646403021⟩, ⟨118325460403, 127030000407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 148111360 149422080 213647360 216596480 ⟨⟨120167340937, 120167340946⟩, ⟨115883150030, 124513664047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 148111360 149422080 216596480 219545600 ⟨⟨121650059773, 121650059780⟩, ⟨117356552844, 126005609154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 146800640 148111360 219545600 225443840 ⟨⟨124878389806, 124878389810⟩, ⟨119503678162, 130350122054⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 148111360 149422080 219545600 225443840 ⟨⟨123867485613, 123867485620⟩, ⟨118530432296, 129300521688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 149422080 150732800 213647360 216596480 ⟨⟨119189890590, 119189890599⟩, ⟨114932756724, 123508550155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 149422080 150732800 216596480 219545600 ⟨⟨120662853451, 120662853458⟩, ⟨116396412635, 124990734722⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 150732800 152043520 213647360 216596480 ⟨⟨118221371118, 118221371125⟩, ⟨113990930922, 122512740738⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 150732800 152043520 216596480 219545600 ⟨⟨119684619425, 119684619432⟩, ⟨115444882610, 123985204786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 149422080 150732800 219545600 225443840 ⟨⟨122865778190, 122865778199⟩, ⟨117565894333, 128260624276⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 150732800 152043520 219545600 222494720 ⟨⟨121144455574, 121144455582⟩, ⟨116895465020, 125454213259⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 150732800 152043520 222494720 225443840 ⟨⟨122600907224, 122600907231⟩, ⟨118342705354, 126919794269⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 152043520 213647360 225443840 t = true :=
  ⟨_, (join_su (m := 149422080) (by decide) (join_sr (m := 219545600) (by decide) (join_su (m := 148111360) (by decide) (join_sr (m := 216596480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 216596480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 148111360) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 219545600) (by decide) (join_su (m := 150732800) (by decide) (join_sr (m := 216596480) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 216596480) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 150732800) (by decide) (leaf_ok cell10) (join_sr (m := 222494720) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (163/640 : ℝ) (43/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((213647360 : ℤ) : ℝ) / (D : ℝ)) = (163/640 : ℝ) := by norm_num [D]
  have e3 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

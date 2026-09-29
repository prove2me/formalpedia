-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_243793920_r292945920_304087040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:28:59.090035+00:00
-- url     : https://prove2.me/submissions/97f4218b-84d8-4a08-963a-ab28fc6a5662

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 93/320]`, `ρ ∈ [447/1280, 29/80]` by 15 cells of the computing
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
theorem cell0 : cellOK 241172480 241827840 292945920 295731200 ⟨⟨89955447332, 89955447339⟩, ⟨88125124884, 91798327670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241827840 242483200 292945920 295731200 ⟨⟨89557166920, 89557166926⟩, ⟨87731399819, 91395449693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241172480 241827840 295731200 298516480 ⟨⟨90769930262, 90769930269⟩, ⟨88935972525, 92616454166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 241827840 242483200 295731200 298516480 ⟨⟨90368350018, 90368350025⟩, ⟨88538955642, 92210268472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 242483200 243138560 292945920 295731200 ⟨⟨89159751257, 89159751264⟩, ⟨87338521526, 90993454661⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 243138560 243793920 292945920 295731200 ⟨⟨88763194500, 88763194507⟩, ⟨86946484276, 90592336617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 242483200 243138560 295731200 298516480 ⟨⟨89967637889, 89967637896⟩, ⟨88142788911, 91804969067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 243138560 243793920 295731200 298516480 ⟨⟨89567788017, 89567788024⟩, ⟨87747466598, 91400549981⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 241172480 241827840 298516480 301301760 ⟨⟨91583836504, 91583836511⟩, ⟨89746245312, 93434002083⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 241827840 242483200 298516480 301301760 ⟨⟨91178963480, 91178963487⟩, ⟨89345943603, 93024515783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 241172480 242483200 301301760 304087040 ⟨⟨92192979779, 92192979785⟩, ⟨89028827158, 95393220785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 242483200 243138560 298516480 301301760 ⟨⟨90774961869, 90774961876⟩, ⟨88946495365, 92615919048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243138560 243793920 298516480 301301760 ⟨⟨90371825804, 90371825809⟩, ⟨88547894851, 92208205897⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 242483200 243138560 301301760 304087040 ⟨⟨91581725935, 91581725941⟩, ⟨89749643613, 93426307353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 243138560 243793920 301301760 304087040 ⟨⟨91175310554, 91175310559⟩, ⟨89347771722, 93015307073⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 243793920 292945920 304087040 t = true :=
  ⟨_, (join_sr (m := 298516480) (by decide) (join_su (m := 242483200) (by decide) (join_sr (m := 295731200) (by decide) (join_su (m := 241827840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 241827840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 295731200) (by decide) (join_su (m := 243138560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 243138560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 242483200) (by decide) (join_sr (m := 301301760) (by decide) (join_su (m := 241827840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 301301760) (by decide) (join_su (m := 243138560) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 243138560) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (447/1280 : ℝ) (29/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  have e3 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

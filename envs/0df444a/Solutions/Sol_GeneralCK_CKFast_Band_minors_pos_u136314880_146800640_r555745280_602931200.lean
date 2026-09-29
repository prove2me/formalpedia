-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_146800640_r555745280_602931200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:53:19.740443+00:00
-- url     : https://prove2.me/submissions/70732e62-7ba0-4c0e-9f7f-786cb24f7b67

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 7/40]`, `ρ ∈ [53/80, 23/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 138936320 555745280 567541760 ⟨⟨291763717598, 291763717603⟩, ⟨278776686392, 305046123956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 138936320 141557760 555745280 567541760 ⟨⟨288027377806, 288027377817⟩, ⟨275177894251, 301170276172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 136314880 138936320 567541760 579338240 ⟨⟨296770345555, 296770345559⟩, ⟨283736365745, 310095347564⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 138936320 141557760 567541760 579338240 ⟨⟨292995320506, 292995320517⟩, ⟨280097653366, 306182248373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 141557760 144179200 555745280 567541760 ⟨⟨284329657092, 284329657103⟩, ⟨271615674654, 297335074601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 144179200 146800640 555745280 567541760 ⟨⟨280669547594, 280669547605⟩, ⟨268089070064, 293539463432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 141557760 144179200 567541760 579338240 ⟨⟨289258461981, 289258461991⟩, ⟨276495132754, 302309265042⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 144179200 146800640 567541760 579338240 ⟨⟨285558782320, 285558782331⟩, ⟨272927863872, 298475364829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 136314880 138936320 579338240 591134720 ⟨⟨301752863498, 301752863503⟩, ⟨288672468630, 315119927198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 138936320 141557760 579338240 591134720 ⟨⟨297939793090, 297939793101⟩, ⟨284994469920, 311170219370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 136314880 138936320 591134720 602931200 ⟨⟨306712112630, 306712112636⟩, ⟨293585810612, 320120729033⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 138936320 141557760 591134720 602931200 ⟨⟨302861607375, 302861607386⟩, ⟨289869130953, 316135025185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 141557760 144179200 579338240 591134720 ⟨⟨294164428507, 294164428517⟩, ⟨281352272972, 307260090264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 144179200 146800640 579338240 591134720 ⟨⟨290425801995, 290425802006⟩, ⟨277744955045, 303388529779⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 141557760 144179200 591134720 602931200 ⟨⟨299048339894, 299048339905⟩, ⟨286187854604, 312188356907⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 144179200 146800640 591134720 602931200 ⟨⟨295271362018, 295271362030⟩, ⟨282541075914, 308279736316⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 146800640 555745280 602931200 t = true :=
  ⟨_, (join_sr (m := 579338240) (by decide) (join_su (m := 141557760) (by decide) (join_sr (m := 567541760) (by decide) (join_su (m := 138936320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 138936320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 567541760) (by decide) (join_su (m := 144179200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 144179200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 141557760) (by decide) (join_sr (m := 591134720) (by decide) (join_su (m := 138936320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 138936320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 591134720) (by decide) (join_su (m := 144179200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 144179200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (53/80 : ℝ) (23/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((555745280 : ℤ) : ℝ) / (D : ℝ)) = (53/80 : ℝ) := by norm_num [D]
  have e3 : (((602931200 : ℤ) : ℝ) / (D : ℝ)) = (23/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

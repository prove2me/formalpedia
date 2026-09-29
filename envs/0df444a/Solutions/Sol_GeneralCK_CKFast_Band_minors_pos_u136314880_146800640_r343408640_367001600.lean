-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_146800640_r343408640_367001600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:44:57.974969+00:00
-- url     : https://prove2.me/submissions/9daedf68-71ec-48a7-b4c3-fb6297339ff4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 7/40]`, `ρ ∈ [131/320, 7/16]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 138936320 343408640 349306880 ⟨⟨194990312114, 194990312119⟩, ⟨185251744562, 204974482035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136314880 138936320 349306880 355205120 ⟨⟨197809914653, 197809914656⟩, ⟨188041469327, 207822770962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 138936320 141557760 343408640 349306880 ⟨⟨192116760814, 192116760822⟩, ⟨182493947737, 201981539789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 138936320 141557760 349306880 355205120 ⟨⟨194907462376, 194907462386⟩, ⟨185254459857, 204801320645⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 136314880 138936320 355205120 361103360 ⟨⟨200618131168, 200618131172⟩, ⟨190820066432, 210659411897⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 136314880 138936320 361103360 367001600 ⟨⟨203415151631, 203415151636⟩, ⟨193587720100, 213484600639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 138936320 141557760 355205120 361103360 ⟨⟨197687157709, 197687157719⟩, ⟨188004215599, 207609841264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 138936320 141557760 361103360 367001600 ⟨⟨200456027995, 200456028006⟩, ⟨190743390721, 210407288339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 141557760 144179200 343408640 349306880 ⟨⟨189287251235, 189287251243⟩, ⟨179777521414, 199035399544⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 141557760 144179200 349306880 355205120 ⟨⟨192049021968, 192049021977⟩, ⟨182508823608, 201826606028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 144179200 146800640 343408640 349306880 ⟨⟨186500384777, 186500384785⟩, ⟨177101160026, 196134566948⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 144179200 146800640 349306880 355205120 ⟨⟨189233204671, 189233204681⟩, ⟨179803262961, 198897144702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 141557760 144179200 355205120 361103360 ⟨⟨194800156236, 194800156246⟩, ⟨185229730675, 204606930079⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 141557760 144179200 361103360 367001600 ⟨⟨197540826819, 197540826827⟩, ⟨187940410276, 207376549678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 144179200 146800640 355205120 361103360 ⟨⟨191955748007, 191955748015⟩, ⟨182495322188, 201649208009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 144179200 146800640 361103360 367001600 ⟨⟨194668179525, 194668179535⟩, ⟨185177497625, 204390926516⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 146800640 343408640 367001600 t = true :=
  ⟨_, (join_su (m := 141557760) (by decide) (join_sr (m := 355205120) (by decide) (join_su (m := 138936320) (by decide) (join_sr (m := 349306880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 349306880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 138936320) (by decide) (join_sr (m := 361103360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 361103360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 355205120) (by decide) (join_su (m := 144179200) (by decide) (join_sr (m := 349306880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 349306880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 144179200) (by decide) (join_sr (m := 361103360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 361103360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (131/320 : ℝ) (7/16 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((343408640 : ℤ) : ℝ) / (D : ℝ)) = (131/320 : ℝ) := by norm_num [D]
  have e3 : (((367001600 : ℤ) : ℝ) / (D : ℝ)) = (7/16 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

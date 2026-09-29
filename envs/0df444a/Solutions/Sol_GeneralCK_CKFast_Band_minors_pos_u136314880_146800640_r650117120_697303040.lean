-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_146800640_r650117120_697303040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:54:16.721094+00:00
-- url     : https://prove2.me/submissions/ecce7913-ded8-4652-9bc9-c0fe2b327f30

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 7/40]`, `ρ ∈ [31/40, 133/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 138936320 650117120 661913600 ⟨⟨331187290937, 331187290943⟩, ⟨317838242437, 344796839724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 138936320 141557760 650117120 661913600 ⟨⟨327157818969, 327157818980⟩, ⟨313936314611, 340639371778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 136314880 138936320 661913600 673710080 ⟨⟨336023433003, 336023433009⟩, ⟨322631039549, 349671950004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 138936320 141557760 661913600 673710080 ⟨⟨331959633380, 331959633391⟩, ⟨318693522107, 345481592685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 141557760 144179200 650117120 661913600 ⟨⟨323163158123, 323163158134⟩, ⟨310067695306, 336518156895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 144179200 146800640 650117120 661913600 ⟨⟨319202453290, 319202453303⟩, ⟨306231560803, 332432311825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 141557760 144179200 661913600 673710080 ⟨⟨327930146437, 327930146450⟩, ⟨314788877945, 341326922631⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 144179200 146800640 661913600 673710080 ⟨⟨323934134684, 323934134695⟩, ⟨310916298990, 337207076229⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 136314880 138936320 673710080 685506560 ⟨⟨340841633048, 340841633054⟩, ⟨327406248650, 354528757625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 138936320 141557760 673710080 685506560 ⟨⟨336743940033, 336743940044⟩, ⟨323433575268, 350305943340⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 136314880 138936320 685506560 697303040 ⟨⟨345642581704, 345642581708⟩, ⟨332164541486, 359367971196⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 138936320 141557760 685506560 697303040 ⟨⟨341511407965, 341511407975⟩, ⟨328157124725, 355113110357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 141557760 144179200 673710080 685506560 ⟨⟨332680058093, 332680058105⟩, ⟨319493335724, 346118248584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 144179200 146800640 673710080 685506560 ⟨⟨328649167021, 328649167032⟩, ⟨315584737346, 341964828961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 141557760 144179200 685506560 697303040 ⟨⟨337413540982, 337413540992⟩, ⟨324181698629, 350892799800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 144179200 146800640 685506560 697303040 ⟨⟨333348177496, 333348177505⟩, ⟨320237485663, 346706213928⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 146800640 650117120 697303040 t = true :=
  ⟨_, (join_sr (m := 673710080) (by decide) (join_su (m := 141557760) (by decide) (join_sr (m := 661913600) (by decide) (join_su (m := 138936320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 138936320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 661913600) (by decide) (join_su (m := 144179200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 144179200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 141557760) (by decide) (join_sr (m := 685506560) (by decide) (join_su (m := 138936320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 138936320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 685506560) (by decide) (join_su (m := 144179200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 144179200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (31/40 : ℝ) (133/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((650117120 : ℤ) : ℝ) / (D : ℝ)) = (31/40 : ℝ) := by norm_num [D]
  have e3 : (((697303040 : ℤ) : ℝ) / (D : ℝ)) = (133/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

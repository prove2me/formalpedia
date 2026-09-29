-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u141557760_144179200_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:28:46.414509+00:00
-- url     : https://prove2.me/submissions/68dc2e4a-b82f-4b8f-a73a-293e6454ba97

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [27/160, 11/64]`, `ρ ∈ [109/640, 59/320]` by 15 cells of the computing
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
theorem cell0 : cellOK 141557760 142213120 142868480 145817600 ⟨⟨87341749229, 87341749236⟩, ⟨84705260107, 90005209021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 142213120 142868480 142868480 145817600 ⟨⟨86959961024, 86959961028⟩, ⟨84333446897, 89613273675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 141557760 142213120 145817600 148766720 ⟨⟨88982328852, 88982328859⟩, ⟨86339796684, 91651774446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 142213120 142868480 145817600 148766720 ⟨⟨88594438804, 88594438808⟩, ⟨85961891737, 91253728398⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 142868480 143523840 142868480 145817600 ⟨⟨86580273187, 86580273194⟩, ⟨83963659744, 89223514749⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 143523840 144179200 142868480 145817600 ⟨⟨86202664093, 86202664100⟩, ⟨83595877880, 88835909734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 142868480 143523840 145817600 148766720 ⟨⟨88208670923, 88208670930⟩, ⟨85586034813, 90857880379⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 143523840 144179200 145817600 148766720 ⟨⟨87825003447, 87825003456⟩, ⟨85212205003, 90464207750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 141557760 142213120 148766720 151715840 ⟨⟨90618025255, 90618025264⟩, ⟨87969495118, 93293411418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 142213120 142868480 148766720 151715840 ⟨⟨90224086690, 90224086693⟩, ⟨87585551147, 92889308595⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 141557760 142868480 151715840 154664960 ⟨⟨92048643426, 92048643433⟩, ⟨87832464540, 96332422352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 142868480 143523840 148766720 151715840 ⟨⟨89832291503, 89832291510⟩, ⟨87203676590, 92487424821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 143523840 144179200 148766720 151715840 ⟨⟨89442617810, 89442617817⟩, ⟨86823850403, 92087737333⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 142868480 143523840 151715840 154664960 ⟨⟨91451177659, 91451177666⟩, ⟨88816627248, 94112191373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 143523840 144179200 151715840 154664960 ⟨⟨91055549245, 91055549252⟩, ⟨88430855596, 93706541103⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 141557760 144179200 142868480 154664960 t = true :=
  ⟨_, (join_sr (m := 148766720) (by decide) (join_su (m := 142868480) (by decide) (join_sr (m := 145817600) (by decide) (join_su (m := 142213120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 142213120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 145817600) (by decide) (join_su (m := 143523840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 143523840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 142868480) (by decide) (join_sr (m := 151715840) (by decide) (join_su (m := 142213120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 151715840) (by decide) (join_su (m := 143523840) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 143523840) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (27/160 : ℝ) (11/64 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e1 : (((144179200 : ℤ) : ℝ) / (D : ℝ)) = (11/64 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

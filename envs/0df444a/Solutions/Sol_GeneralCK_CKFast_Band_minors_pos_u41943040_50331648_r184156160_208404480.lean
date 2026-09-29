-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u41943040_50331648_r184156160_208404480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:50:05.498388+00:00
-- url     : https://prove2.me/submissions/14cf1f00-aa5a-4fce-a8b5-a159ab7ce650

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/20, 3/50]`, `ρ ∈ [281/1280, 159/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 41943040 44040192 184156160 190218240 ⟨⟨235225919424, 235225919439⟩, ⟨219208779697, 251901021988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 41943040 44040192 190218240 196280320 ⟨⟨240346609893, 240346609911⟩, ⟨224370837313, 256963257093⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 44040192 46137344 184156160 190218240 ⟨⟨230366838681, 230366838695⟩, ⟨214748284269, 246619275898⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 44040192 46137344 190218240 196280320 ⟨⟨235455116342, 235455116358⟩, ⟨219870921892, 251657357516⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 41943040 44040192 196280320 202342400 ⟨⟨245384267612, 245384267625⟩, ⟨229450528260, 261942350345⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 41943040 44040192 202342400 208404480 ⟨⟨250342307690, 250342307707⟩, ⟨234451153203, 266841807334⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 44040192 46137344 196280320 202342400 ⟨⟨240462808168, 240462808184⟩, ⟨224913772042, 256614548255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 44040192 46137344 202342400 208404480 ⟨⟨245393154602, 245393154619⟩, ⟨229879961621, 261494181893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 46137344 48234496 184156160 190218240 ⟨⟨225696559244, 225696559258⟩, ⟨210456520516, 241547742209⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 46137344 48234496 190218240 196280320 ⟨⟨230750460100, 230750460117⟩, ⟨215538428949, 246558943681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 48234496 50331648 184156160 190218240 ⟨⟨221202879975, 221202879988⟩, ⟨206322797684, 236672614842⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 48234496 50331648 190218240 196280320 ⟨⟨226220721959, 226220721975⟩, ⟨211362882174, 241654569936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 46137344 48234496 196280320 202342400 ⟨⟨235726187677, 235726187691⟩, ⟨220543069614, 251491503650⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 46137344 48234496 202342400 208404480 ⟨⟨240626816082, 240626816099⟩, ⟨225473404904, 256348590929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 48234496 50331648 196280320 202342400 ⟨⟨231162761977, 231162761993⟩, ⟨216328155989, 246560119672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 48234496 50331648 202342400 208404480 ⟨⟨236031915989, 236031916005⟩, ⟨221221425874, 251392274909⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 41943040 50331648 184156160 208404480 t = true :=
  ⟨_, (join_su (m := 46137344) (by decide) (join_sr (m := 196280320) (by decide) (join_su (m := 44040192) (by decide) (join_sr (m := 190218240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 190218240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 44040192) (by decide) (join_sr (m := 202342400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 202342400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 196280320) (by decide) (join_su (m := 48234496) (by decide) (join_sr (m := 190218240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 190218240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 48234496) (by decide) (join_sr (m := 202342400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 202342400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/20 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (281/1280 : ℝ) (159/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  have e3 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

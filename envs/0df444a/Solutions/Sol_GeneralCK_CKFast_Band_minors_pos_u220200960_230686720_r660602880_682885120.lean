-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_230686720_r660602880_682885120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:03:30.833988+00:00
-- url     : https://prove2.me/submissions/0873c53f-f7e5-4a90-a9ab-5d2e8f8f3146

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 11/40]`, `ρ ∈ [63/80, 521/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 222822400 660602880 666173440 ⟨⟨218295502810, 218295502819⟩, ⟨209789319790, 226964036086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 222822400 666173440 671744000 ⟨⟨219974624925, 219974624935⟩, ⟨211441650594, 228669884428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 225443840 660602880 666173440 ⟨⟨215031942665, 215031942674⟩, ⟨206590529717, 223635135774⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 222822400 225443840 666173440 671744000 ⟨⟨216690292537, 216690292547⟩, ⟨208222101173, 225320222360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 222822400 671744000 677314560 ⟨⟨221652282229, 221652282240⟩, ⟨213092530753, 230374249266⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 222822400 677314560 682885120 ⟨⟨223328496715, 223328496724⟩, ⟨214741981881, 232077152949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222822400 225443840 671744000 677314560 ⟨⟨218347234055, 218347234064⟩, ⟨209852276621, 227003883829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222822400 225443840 677314560 682885120 ⟨⟨220002788256, 220002788265⟩, ⟨211481076744, 228686141549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 228065280 660602880 666173440 ⟨⟨211785069262, 211785069271⟩, ⟨203407848676, 220323492836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 225443840 228065280 666173440 671744000 ⟨⟨213422568197, 213422568206⟩, ⟨205018591154, 221987729258⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 230686720 660602880 666173440 ⟨⟨208554521771, 208554521775⟩, ⟨200240925733, 217028736944⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228065280 230686720 666173440 671744000 ⟨⟨210171093684, 210171093689⟩, ⟨201830771963, 218672037653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 225443840 228065280 671744000 677314560 ⟨⟨215058713843, 215058713852⟩, ⟨206627990901, 223650597524⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 225443840 228065280 677314560 682885120 ⟨⟨216693526315, 216693526324⟩, ⟨208236067705, 225312118059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228065280 230686720 671744000 677314560 ⟨⟨211786365992, 211786365996⟩, ⟨203419327400, 220314025755⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 228065280 230686720 677314560 682885120 ⟨⟨213400357917, 213400357922⟩, ⟨205006610955, 221954720762⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 230686720 660602880 682885120 t = true :=
  ⟨_, (join_su (m := 225443840) (by decide) (join_sr (m := 671744000) (by decide) (join_su (m := 222822400) (by decide) (join_sr (m := 666173440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 666173440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 222822400) (by decide) (join_sr (m := 677314560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 677314560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 671744000) (by decide) (join_su (m := 228065280) (by decide) (join_sr (m := 666173440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 666173440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 228065280) (by decide) (join_sr (m := 677314560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 677314560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (63/80 : ℝ) (521/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((660602880 : ℤ) : ℝ) / (D : ℝ)) = (63/80 : ℝ) := by norm_num [D]
  have e3 : (((682885120 : ℤ) : ℝ) / (D : ℝ)) = (521/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u25165824_33554432_r184156160_208404480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:28:17.987806+00:00
-- url     : https://prove2.me/submissions/cfdd44b0-c500-4c7f-9af7-dc039752ab69

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/100, 1/25]`, `ρ ∈ [281/1280, 159/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 25165824 27262976 184156160 190218240 ⟨⟨282870216014, 282870216019⟩, ⟨262685529500, 303967713362⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 25165824 27262976 190218240 196280320 ⟨⟨288128037646, 288128037660⟩, ⟨268076479694, 309059457336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 27262976 29360128 184156160 190218240 ⟨⟨275864550774, 275864550795⟩, ⟨256322646338, 296280143746⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 27262976 29360128 190218240 196280320 ⟨⟨281122681751, 281122681772⟩, ⟨261697658560, 301391203875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 25165824 27262976 196280320 202342400 ⟨⟨293283753422, 293283753435⟩, ⟨273363268882, 314052688061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 25165824 27262976 202342400 208404480 ⟨⟨298342447594, 298342447608⟩, ⟨278550945420, 318952429298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 27262976 29360128 196280320 202342400 ⟨⟨286280817763, 286280817784⟩, ⟨266971210610, 306405081029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 27262976 29360128 202342400 208404480 ⟨⟨291343815796, 291343815817⟩, ⟨272148098563, 311326612414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 29360128 31457280 184156160 190218240 ⟨⟨269210497982, 269210497998⟩, ⟨250269362858, 288988547823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 29360128 31457280 190218240 196280320 ⟨⟨274462416486, 274462416503⟩, ⟨255623639645, 294110399133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 31457280 33554432 184156160 190218240 ⟨⟨262878276760, 262878276781⟩, ⟨244500157302, 282058751114⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 31457280 33554432 190218240 196280320 ⟨⟨268118377900, 268118377919⟩, ⟨249829603392, 287184033918⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 29360128 31457280 196280320 202342400 ⟨⟨279616597681, 279616597701⟩, ⟨260879206991, 299136667201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 29360128 31457280 202342400 208404480 ⟨⟨284677673520, 284677673537⟩, ⟨266040617367, 304071995798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 31457280 33554432 196280320 202342400 ⟨⟨273263102456, 273263102476⟩, ⟨255063112694, 292215539376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 31457280 33554432 202342400 208404480 ⟨⟨278316861805, 278316861824⟩, ⟨260205003648, 297157714991⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 25165824 33554432 184156160 208404480 t = true :=
  ⟨_, (join_su (m := 29360128) (by decide) (join_sr (m := 196280320) (by decide) (join_su (m := 27262976) (by decide) (join_sr (m := 190218240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 190218240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 27262976) (by decide) (join_sr (m := 202342400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 202342400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 196280320) (by decide) (join_su (m := 31457280) (by decide) (join_sr (m := 190218240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 190218240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 31457280) (by decide) (join_sr (m := 202342400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 202342400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/100 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (281/1280 : ℝ) (159/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  have e3 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

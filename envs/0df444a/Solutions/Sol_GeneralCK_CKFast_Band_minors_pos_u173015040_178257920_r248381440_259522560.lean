-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u173015040_178257920_r248381440_259522560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:18:41.449986+00:00
-- url     : https://prove2.me/submissions/cfe271fd-3334-4444-93c3-6b8d8a3b9a17

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/160, 17/80]`, `ρ ∈ [379/1280, 99/320]` by 9 cells of the computing
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
theorem cell0 : cellOK 173015040 174325760 248381440 253952000 ⟨⟨118760503147, 118760503152⟩, ⟨114058118743, 123538078130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 174325760 175636480 248381440 253952000 ⟨⟨117821795049, 117821795055⟩, ⟨113148208890, 122569896740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 173015040 174325760 253952000 259522560 ⟨⟨121168842900, 121168842905⟩, ⟨116448746091, 125963981051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 174325760 175636480 253952000 259522560 ⟨⟨120214256060, 120214256067⟩, ⟨115522991474, 124979894931⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 175636480 176947200 248381440 253952000 ⟨⟨116889908988, 116889908996⟩, ⟨112244804599, 121608863365⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 176947200 178257920 248381440 251166720 ⟨⟨115373362908, 115373362915⟩, ⟨111554250038, 119241786290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 176947200 178257920 251166720 253952000 ⟨⟨116555646333, 116555646341⟩, ⟨112728442704, 120432141986⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 175636480 176947200 253952000 259522560 ⟨⟨119266541249, 119266541258⟩, ⟨114603794185, 124003004826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 176947200 178257920 253952000 259522560 ⟨⟨118325591008, 118325591015⟩, ⟨113691052111, 123033197744⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 173015040 178257920 248381440 259522560 t = true :=
  ⟨_, (join_su (m := 175636480) (by decide) (join_sr (m := 253952000) (by decide) (join_su (m := 174325760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 174325760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 253952000) (by decide) (join_su (m := 176947200) (by decide) (leaf_ok cell4) (join_sr (m := 251166720) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 176947200) (by decide) (leaf_ok cell7) (leaf_ok cell8))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/160 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (379/1280 : ℝ) (99/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  have e3 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

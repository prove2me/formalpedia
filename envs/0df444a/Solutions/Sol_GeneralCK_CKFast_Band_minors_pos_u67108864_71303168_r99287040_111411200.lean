-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_71303168_r99287040_111411200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:29:36.704709+00:00
-- url     : https://prove2.me/submissions/9c5f1e4e-1c5c-400d-be18-b79b1dcb7cf5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 17/200]`, `ρ ∈ [303/2560, 17/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 67108864 68157440 99287040 102318080 ⟨⟨113992884543, 113992884556⟩, ⟨107920791506, 120206317100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 67108864 68157440 102318080 105349120 ⟨⟨116874017293, 116874017304⟩, ⟨110792212275, 123095954077⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 68157440 69206016 99287040 102318080 ⟨⟨112809797601, 112809797614⟩, ⟨106805374445, 118952791699⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 68157440 69206016 102318080 105349120 ⟨⟨115669516735, 115669516745⟩, ⟨109655180770, 121821264920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 67108864 68157440 105349120 108380160 ⟨⟨119730767112, 119730767125⟩, ⟨113639657778, 125960810701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 67108864 68157440 108380160 111411200 ⟨⟨122563613717, 122563613728⟩, ⟨116463593194, 128801381235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 68157440 69206016 105349120 108380160 ⟨⟨118505390124, 118505390135⟩, ⟨112481539948, 124665503266⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 68157440 69206016 108380160 111411200 ⟨⟨121317881053, 121317881063⟩, ⟨115284901303, 127485983996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 69206016 70254592 99287040 102318080 ⟨⟨111649033072, 111649033082⟩, ⟨105710668953, 117723285925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 69206016 70254592 102318080 105349120 ⟨⟨114487542272, 114487542282⟩, ⟨108539079631, 120570781649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 70254592 71303168 99287040 102318080 ⟨⟨110509901686, 110509901699⟩, ⟨104636043032, 116517049620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 70254592 71303168 102318080 105349120 ⟨⟨113327403692, 113327403702⟩, ⟨107443274990, 119343754218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 69206016 70254592 105349120 108380160 ⟨⟨117302728874, 117302728885⟩, ⟨111344557384, 123394573848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 69206016 70254592 108380160 111411200 ⟨⟨120095040382, 120095040392⟩, ⟨114127536312, 126195123449⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 70254592 71303168 105349120 108380160 ⟨⟨116122092643, 116122092653⟩, ⟨110228074789, 122147272936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 70254592 71303168 108380160 111411200 ⟨⟨118894400877, 118894400890⟩, ⟨112990861905, 124928051016⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 71303168 99287040 111411200 t = true :=
  ⟨_, (join_su (m := 69206016) (by decide) (join_sr (m := 105349120) (by decide) (join_su (m := 68157440) (by decide) (join_sr (m := 102318080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 102318080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 68157440) (by decide) (join_sr (m := 108380160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 108380160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 105349120) (by decide) (join_su (m := 70254592) (by decide) (join_sr (m := 102318080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 102318080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 70254592) (by decide) (join_sr (m := 108380160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 108380160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (17/200 : ℝ) →
    rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((71303168 : ℤ) : ℝ) / (D : ℝ)) = (17/200 : ℝ) := by norm_num [D]
  have e2 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  have e3 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

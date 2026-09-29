-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_225443840_r315228160_326369280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:07:04.96498+00:00
-- url     : https://prove2.me/submissions/82dfb5bf-5c76-4013-b377-d9e43443b023

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 43/160]`, `ρ ∈ [481/1280, 249/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 221511680 315228160 318013440 ⟨⟨110318047055, 110318047061⟩, ⟨106893997411, 113781729804⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 221511680 318013440 320798720 ⟨⟨111231701975, 111231701983⟩, ⟨107800506735, 114702553964⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 221511680 222822400 315228160 318013440 ⟨⟨109407552405, 109407552411⟩, ⟨105998556835, 112855954132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 221511680 222822400 318013440 320798720 ⟨⟨110314534039, 110314534046⟩, ⟨106898415110, 113770083771⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 221511680 320798720 323584000 ⟨⟨112144556359, 112144556366⟩, ⟨108706220900, 115622571964⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 221511680 323584000 326369280 ⟨⟨113056614498, 113056614505⟩, ⟨109611144163, 116541788130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 221511680 222822400 320798720 323584000 ⟨⟨111220732885, 111220732893⟩, ⟨107797495724, 114683425255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 221511680 222822400 323584000 326369280 ⟨⟨112126153118, 112126153125⟩, ⟨108695802823, 115595982785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 222822400 224133120 315228160 318013440 ⟨⟨108501425988, 108501425994⟩, ⟨105107353344, 111934680280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 222822400 224133120 318013440 320798720 ⟨⟨109401746591, 109401746598⟩, ⟨106000573095, 112842127358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 224133120 225443840 315228160 318013440 ⟨⟨107599609147, 107599609153⟩, ⟨104220330035, 111017847796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 224133120 225443840 318013440 320798720 ⟨⟨108493280929, 108493280937⟩, ⟨105106923737, 111918624237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 222822400 224133120 320798720 323584000 ⟨⟨110301301849, 110301301855⟩, ⟨106893032383, 113748803970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 222822400 224133120 323584000 326369280 ⟨⟨111200095819, 111200095826⟩, ⟨107784735239, 114654714208⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224133120 225443840 320798720 323584000 ⟨⟨109386204507, 109386204514⟩, ⟨105992773876, 112818647598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 224133120 225443840 323584000 326369280 ⟨⟨110278383827, 110278383834⟩, ⟨106877884374, 113717921854⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 225443840 315228160 326369280 t = true :=
  ⟨_, (join_su (m := 222822400) (by decide) (join_sr (m := 320798720) (by decide) (join_su (m := 221511680) (by decide) (join_sr (m := 318013440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 318013440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 221511680) (by decide) (join_sr (m := 323584000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 323584000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 320798720) (by decide) (join_su (m := 224133120) (by decide) (join_sr (m := 318013440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 318013440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 224133120) (by decide) (join_sr (m := 323584000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 323584000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (481/1280 : ℝ) (249/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((315228160 : ℤ) : ℝ) / (D : ℝ)) = (481/1280 : ℝ) := by norm_num [D]
  have e3 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

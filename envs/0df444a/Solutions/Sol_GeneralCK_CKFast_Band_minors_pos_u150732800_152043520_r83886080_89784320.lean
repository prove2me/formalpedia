-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u150732800_152043520_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:59:54.865707+00:00
-- url     : https://prove2.me/submissions/1eeee429-d416-4c61-b2cd-2688e2df3e96

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/128, 29/160]`, `ρ ∈ [1/10, 137/1280]` by 12 cells of the computing
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
theorem cell0 : cellOK 150732800 151060480 83886080 85360640 ⟨⟨49744801986, 49744801992⟩, ⟨48552881327, 50943110438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 151060480 151388160 83886080 85360640 ⟨⟨49631565525, 49631565533⟩, ⟨48441823034, 50827674494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 150732800 151060480 85360640 86835200 ⟨⟨50571359756, 50571359762⟩, ⟨49377750299, 51771352344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 151060480 151388160 85360640 86835200 ⟨⟨50456398620, 50456398626⟩, ⟨49264970410, 51654188705⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 151388160 151715840 83886080 85360640 ⟨⟨49518655770, 49518655773⟩, ⟨48331083333, 50712573475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 151715840 152043520 83886080 85360640 ⟨⟨49406070958, 49406070964⟩, ⟨48220660511, 50597805583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 151388160 151715840 85360640 86835200 ⟨⟨50341768257, 50341768260⟩, ⟨49152513181, 51537364064⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 151715840 152043520 85360640 86835200 ⟨⟨50227466887, 50227466895⟩, ⟨49040376875, 51420876602⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 150732800 151388160 86835200 88309760 ⟨⟨51338279001, 51338279008⟩, ⟨49437371570, 53255185222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 150732800 151388160 88309760 89784320 ⟨⟨52161472185, 52161472193⟩, ⟨50257638093, 54081298750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 151388160 152043520 86835200 88309760 ⟨⟨51105591412, 51105591420⟩, ⟨49210910766, 53016173908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 151388160 152043520 88309760 89784320 ⟨⟨51925372888, 51925372896⟩, ⟨50027775368, 53838866195⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 150732800 152043520 83886080 89784320 t = true :=
  ⟨_, (join_sr (m := 86835200) (by decide) (join_su (m := 151388160) (by decide) (join_sr (m := 85360640) (by decide) (join_su (m := 151060480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 151060480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 85360640) (by decide) (join_su (m := 151715840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 151715840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 151388160) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 88309760) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/128 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((150732800 : ℤ) : ℝ) / (D : ℝ)) = (23/128 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

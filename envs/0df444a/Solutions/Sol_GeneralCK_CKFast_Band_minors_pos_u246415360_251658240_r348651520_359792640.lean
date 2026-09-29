-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_251658240_r348651520_359792640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:00:22.374684+00:00
-- url     : https://prove2.me/submissions/8673d2f0-7d23-478e-adee-8fc56efc2151

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 3/10]`, `ρ ∈ [133/320, 549/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247726080 348651520 351436800 ⟨⟨102232259239, 102232259246⟩, ⟨99006422614, 105494081247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246415360 247726080 351436800 354222080 ⟨⟨103008886326, 103008886333⟩, ⟨99776406035, 106277389716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247726080 249036800 348651520 351436800 ⟨⟨101322426600, 101322426606⟩, ⟨98109628001, 104571033962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247726080 249036800 351436800 354222080 ⟨⟨102092759044, 102092759052⟩, ⟨98873341161, 105348024062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 246415360 247726080 354222080 357007360 ⟨⟨103785042763, 103785042769⟩, ⟨100545919936, 107060226245⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246415360 247726080 357007360 359792640 ⟨⟨104560730879, 104560730887⟩, ⟨101314966637, 107842593174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247726080 249036800 354222080 357007360 ⟨⟨102862632377, 102862632384⟩, ⟨99636596184, 106124553917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247726080 249036800 357007360 359792640 ⟨⟨103632048858, 103632048865⟩, ⟨100399395322, 106900625798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 250347520 348651520 351436800 ⟨⟨100416052439, 100416052445⟩, ⟨97216192662, 103651546019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249036800 250347520 351436800 354222080 ⟨⟨101180098657, 101180098664⟩, ⟨97973644158, 104422225967⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 250347520 251658240 348651520 351436800 ⟨⟨99513091729, 99513091737⟩, ⟨96326072765, 102735571180⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 250347520 251658240 351436800 354222080 ⟨⟨100270860100, 100270860107⟩, ⟨97077271154, 103499949157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249036800 250347520 354222080 357007360 ⟨⟨101943697089, 101943697095⟩, ⟨98730648692, 105192457148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 249036800 250347520 357007360 359792640 ⟨⟨102706849929, 102706849936⟩, ⟨99487208454, 105962241770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 250347520 251658240 354222080 357007360 ⟨⟨101028191800, 101028191807⟩, ⟨97828033552, 104263889639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250347520 251658240 357007360 359792640 ⟨⟨101785088964, 101785088971⟩, ⟨98578362086, 105027394766⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 251658240 348651520 359792640 t = true :=
  ⟨_, (join_su (m := 249036800) (by decide) (join_sr (m := 354222080) (by decide) (join_su (m := 247726080) (by decide) (join_sr (m := 351436800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 351436800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 247726080) (by decide) (join_sr (m := 357007360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 357007360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 354222080) (by decide) (join_su (m := 250347520) (by decide) (join_sr (m := 351436800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 351436800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 250347520) (by decide) (join_sr (m := 357007360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 357007360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (133/320 : ℝ) (549/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  have e3 : (((359792640 : ℤ) : ℝ) / (D : ℝ)) = (549/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

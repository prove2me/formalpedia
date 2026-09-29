-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_178257920_r660602880_705167360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:26:59.015598+00:00
-- url     : https://prove2.me/submissions/d8d22454-002c-4008-8765-999d729c3eb8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 17/80]`, `ρ ∈ [63/80, 269/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 170393600 660602880 671744000 ⟨⟨288741350342, 288741350352⟩, ⟨276993806884, 300729698342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 170393600 173015040 660602880 671744000 ⟨⟨285044952232, 285044952245⟩, ⟨273404867738, 296925023899⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 167772160 170393600 671744000 682885120 ⟨⟨292881797539, 292881797550⟩, ⟨281083039759, 304919075104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 170393600 173015040 671744000 682885120 ⟨⟨289148598313, 289148598324⟩, ⟨277456719990, 301078296559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 173015040 175636480 660602880 671744000 ⟨⟨281374430003, 281374430013⟩, ⟨269840689502, 293147307791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 175636480 178257920 660602880 671744000 ⟨⟨277729202950, 277729202956⟩, ⟨266300711409, 289395951080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 173015040 175636480 671744000 682885120 ⟨⟨285440962296, 285440962306⟩, ⟨273854888297, 297264120837⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 175636480 178257920 671744000 682885120 ⟨⟨281758319211, 281758319218⟩, ⟨270276993158, 293475960655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 167772160 170393600 682885120 694026240 ⟨⟨297010979578, 297010979588⟩, ⟨285161255829, 309096915792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 170393600 173015040 682885120 694026240 ⟨⟨293241305748, 293241305758⟩, ⟨281497874688, 305220366393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 167772160 170393600 694026240 705167360 ⟨⟨301129279501, 301129279511⟩, ⟨289228827850, 313263613455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 170393600 173015040 694026240 705167360 ⟨⟨297323444156, 297323444165⟩, ⟨285528691560, 309351612652⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 173015040 175636480 682885120 694026240 ⟨⟨289496877609, 289496877619⟩, ⟨277858703662, 301370059825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 175636480 178257920 682885120 694026240 ⟨⟨285777135208, 285777135214⟩, ⟨274243200406, 297545420316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 173015040 175636480 694026240 705167360 ⟨⟨293542532479, 293542532488⟩, ⟨281852482634, 305465490547⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 175636480 178257920 694026240 705167360 ⟨⟨289785994733, 289785994736⟩, ⟨278199667827, 301604682738⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 178257920 660602880 705167360 t = true :=
  ⟨_, (join_sr (m := 682885120) (by decide) (join_su (m := 173015040) (by decide) (join_sr (m := 671744000) (by decide) (join_su (m := 170393600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 170393600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 671744000) (by decide) (join_su (m := 175636480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 175636480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 173015040) (by decide) (join_sr (m := 694026240) (by decide) (join_su (m := 170393600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 170393600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 694026240) (by decide) (join_su (m := 175636480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 175636480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (63/80 : ℝ) (269/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((660602880 : ℤ) : ℝ) / (D : ℝ)) = (63/80 : ℝ) := by norm_num [D]
  have e3 : (((705167360 : ℤ) : ℝ) / (D : ℝ)) = (269/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

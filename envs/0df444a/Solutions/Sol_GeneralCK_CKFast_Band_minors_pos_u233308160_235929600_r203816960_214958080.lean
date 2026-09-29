-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u233308160_235929600_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:50:47.064106+00:00
-- url     : https://prove2.me/submissions/4e6e6d0d-6ec5-4819-b2da-7f74545cf067

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [89/320, 9/32]`, `ρ ∈ [311/1280, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 233308160 233963520 203816960 206602240 ⟨⟨67092514154, 67092514160⟩, ⟨65326892192, 68870973936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 233963520 234618880 203816960 206602240 ⟨⟨66794769120, 66794769121⟩, ⟨65033642700, 68568683969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233308160 233963520 206602240 209387520 ⟨⟨67970050692, 67970050698⟩, ⟨66200607800, 69752340000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 233963520 234618880 206602240 209387520 ⟨⟨67668684930, 67668684933⟩, ⟨65903747661, 69446419353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 234618880 235274240 203816960 206602240 ⟨⟨66497808037, 66497808042⟩, ⟨64741157308, 68267198115⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235274240 235929600 203816960 206602240 ⟨⟨66201625243, 66201625249⟩, ⟨64449430491, 67966510560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 234618880 235274240 206602240 209387520 ⟨⟨67368109292, 67368109299⟩, ⟨65607657790, 69141308992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 235274240 235929600 206602240 209387520 ⟨⟨67068318083, 67068318090⟩, ⟨65312332633, 68837003071⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 233963520 209387520 212172800 ⟨⟨68846805707, 68846805714⟩, ⟨67073544998, 70632921368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 233963520 234618880 209387520 212172800 ⟨⟨68541828810, 68541828813⟩, ⟨66773083721, 70323379715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 233308160 233963520 212172800 214958080 ⟨⟨69722783020, 69722783027⟩, ⟨67945707585, 71512721880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 233963520 234618880 212172800 214958080 ⟨⟨69414204522, 69414204525⟩, ⟨67641654626, 71199568834⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 234618880 235274240 209387520 212172800 ⟨⟨68237648115, 68237648122⟩, ⟨66473398790, 70014654424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 235274240 235929600 209387520 212172800 ⟨⟨67934257894, 67934257901⟩, ⟨66174484618, 69706739617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 234618880 235274240 212172800 214958080 ⟨⟨69106428209, 69106428214⟩, ⟨67338383997, 70887238131⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 235274240 235929600 212172800 214958080 ⟨⟨68799448321, 68799448328⟩, ⟨67035890077, 70575723863⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 233308160 235929600 203816960 214958080 t = true :=
  ⟨_, (join_sr (m := 209387520) (by decide) (join_su (m := 234618880) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 233963520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 233963520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 206602240) (by decide) (join_su (m := 235274240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 235274240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 234618880) (by decide) (join_sr (m := 212172800) (by decide) (join_su (m := 233963520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 233963520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 212172800) (by decide) (join_su (m := 235274240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 235274240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (89/320 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u152043520_157286400_r319815680_343408640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:03:35.508969+00:00
-- url     : https://prove2.me/submissions/5a1bf3e3-9bf8-4600-b7b4-ae09c6562c9a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [29/160, 3/16]`, `ρ ∈ [61/160, 131/320]` by 13 cells of the computing
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
theorem cell0 : cellOK 152043520 153354240 319815680 325713920 ⟨⟨168336603672, 168336603680⟩, ⟨162792622968, 173967441075⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 153354240 154664960 319815680 325713920 ⟨⟨167072325818, 167072325820⟩, ⟨161563789817, 172666982821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 152043520 153354240 325713920 331612160 ⟨⟨171028613512, 171028613521⟩, ⟨165467491149, 176676220260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 153354240 154664960 325713920 331612160 ⟨⟨169749169031, 169749169035⟩, ⟨164223440948, 175360659041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 154664960 155975680 319815680 325713920 ⟨⟨165817336356, 165817336364⟩, ⟨160343856495, 171376210872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 155975680 157286400 319815680 325713920 ⟨⟨164571490071, 164571490078⟩, ⟨159132684364, 170094973259⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 154664960 155975680 325713920 331612160 ⟨⟨168479026345, 168479026355⟩, ⟨162988308018, 174054793153⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 155975680 157286400 325713920 331612160 ⟨⟨167218040940, 167218040949⟩, ⟨161761954300, 172758471468⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 152043520 154664960 331612160 337510400 ⟨⟨173062295914, 173062295922⟩, ⟨164043214887, 182307941700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 152043520 154664960 337510400 343408640 ⟨⟨175727176204, 175727176214⟩, ⟨166676371971, 185003799062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 154664960 155975680 331612160 337510400 ⟨⟨171131131942, 171131131951⟩, ⟨165623315136, 176723649731⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 155975680 157286400 331612160 337510400 ⟨⟨169855180182, 169855180192⟩, ⟨164381949797, 175412419478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 154664960 157286400 337510400 343408640 ⟨⟨173127286878, 173127286887⟩, ⟨164177656818, 182299533430⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 152043520 157286400 319815680 343408640 t = true :=
  ⟨_, (join_sr (m := 331612160) (by decide) (join_su (m := 154664960) (by decide) (join_sr (m := 325713920) (by decide) (join_su (m := 153354240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 153354240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 325713920) (by decide) (join_su (m := 155975680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 155975680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 154664960) (by decide) (join_sr (m := 337510400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 337510400) (by decide) (join_su (m := 155975680) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (29/160 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (61/160 : ℝ) (131/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  have e3 : (((343408640 : ℤ) : ℝ) / (D : ℝ)) = (131/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

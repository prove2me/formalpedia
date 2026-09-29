-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u212336640_214958080_r170393600_175964160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:19:57.149985+00:00
-- url     : https://prove2.me/submissions/b332fd33-1463-4851-b508-4678260c7cb9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [81/320, 41/160]`, `ρ ∈ [13/64, 537/2560]` by 13 cells of the computing
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
theorem cell0 : cellOK 212336640 212992000 170393600 171786240 ⟨⟨64763940191, 64763940197⟩, ⟨63193979090, 66343863041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 212336640 212992000 171786240 173178880 ⟨⟨65269788396, 65269788401⟩, ⟨63697896933, 66851645533⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212992000 213647360 170393600 171786240 ⟨⟨64485912196, 64485912203⟩, ⟨62919581692, 66062167220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212992000 213647360 171786240 173178880 ⟨⟨64989756320, 64989756327⟩, ⟨63421500194, 66567940946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 212336640 212992000 173178880 175964160 ⟨⟨66027986335, 66027986340⟩, ⟨64153073479, 67917451933⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 212992000 213647360 173178880 175964160 ⟨⟨65744954857, 65744954864⟩, ⟨63875140661, 67629258964⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 213647360 214302720 170393600 171786240 ⟨⟨64208776742, 64208776750⟩, ⟨62646057664, 65781383372⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 213647360 214302720 171786240 173178880 ⟨⟨64710621270, 64710621275⟩, ⟨63145981305, 66285152818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214302720 214958080 170393600 171786240 ⟨⟨63932526959, 63932526963⟩, ⟨62373400284, 65501504470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 214302720 214958080 171786240 173178880 ⟨⟨64432376345, 64432376349⟩, ⟨62871333519, 66003274094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 213647360 214302720 173178880 175964160 ⟨⟨65462827062, 65462827068⟩, ⟨63598086201, 67341995435⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 214302720 214958080 173178880 174571520 ⟨⟨64931929914, 64931929915⟩, ⟨63368972072, 66504746749⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 214302720 214958080 174571520 175964160 ⟨⟨65431188454, 65431188459⟩, ⟨63866316730, 67005923230⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 212336640 214958080 170393600 175964160 t = true :=
  ⟨_, (join_su (m := 213647360) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 212992000) (by decide) (join_sr (m := 171786240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 171786240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 212992000) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 173178880) (by decide) (join_su (m := 214302720) (by decide) (join_sr (m := 171786240) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 171786240) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 214302720) (by decide) (leaf_ok cell10) (join_sr (m := 174571520) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (81/320 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (537/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((175964160 : ℤ) : ℝ) / (D : ℝ)) = (537/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

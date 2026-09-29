-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u212336640_214958080_r164823040_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:35:00.484061+00:00
-- url     : https://prove2.me/submissions/c85a7549-e3c4-4a3b-94c7-e7ffd05895ed

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [81/320, 41/160]`, `ρ ∈ [503/2560, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 212336640 212992000 164823040 166215680 ⟨⟨62737466022, 62737466029⟩, ⟨61175238543, 64309639374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 212336640 212992000 166215680 167608320 ⟨⟨63244548439, 63244548446⟩, ⟨61680385721, 64818661026⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212992000 213647360 164823040 166215680 ⟨⟨62467490462, 62467490468⟩, ⟨60908874364, 64036014981⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212992000 213647360 166215680 167608320 ⟨⟨62972554328, 62972554335⟩, ⟨61412007834, 64543013296⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 212336640 212992000 167608320 169000960 ⟨⟨63751321047, 63751321054⟩, ⟨62185224316, 65327371626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 212336640 212992000 169000960 170393600 ⟨⟨64257784685, 64257784692⟩, ⟨62689755161, 65835772019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212992000 213647360 167608320 169000960 ⟨⟨63477312023, 63477312029⟩, ⟨61914836331, 65049704221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 212992000 213647360 169000960 170393600 ⟨⟨63981764372, 63981764377⟩, ⟨62417360677, 65556088586⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 213647360 214302720 164823040 166215680 ⟨⟨62198389147, 62198389153⟩, ⟨60643365273, 63763284257⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 213647360 214302720 166215680 167608320 ⟨⟨62701439091, 62701439098⟩, ⟨61144489659, 64268263864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 214302720 214958080 164823040 166215680 ⟨⟨61930155314, 61930155318⟩, ⟨60378704658, 63491440280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 214302720 214958080 166215680 167608320 ⟨⟨62431195939, 62431195940⟩, ⟨60877824558, 63994405785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 213647360 214302720 167608320 169000960 ⟨⟨63204186465, 63204186470⟩, ⟨61645312647, 64772939708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 213647360 214302720 169000960 170393600 ⟨⟨63706632078, 63706632083⟩, ⟨62145835046, 65277312606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 214302720 214958080 167608320 169000960 ⟨⟨62931937553, 62931937557⟩, ⟨61376646598, 64497071115⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 214302720 214958080 169000960 170393600 ⟨⟨63432380960, 63432380964⟩, ⟨61875171575, 64999437076⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 212336640 214958080 164823040 170393600 t = true :=
  ⟨_, (join_su (m := 213647360) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 212992000) (by decide) (join_sr (m := 166215680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 166215680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 212992000) (by decide) (join_sr (m := 169000960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 169000960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 167608320) (by decide) (join_su (m := 214302720) (by decide) (join_sr (m := 166215680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 166215680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 214302720) (by decide) (join_sr (m := 169000960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 169000960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (81/320 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (503/2560 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

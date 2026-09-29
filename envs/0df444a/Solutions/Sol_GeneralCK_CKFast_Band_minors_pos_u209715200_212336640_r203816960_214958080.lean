-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_212336640_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:36:48.37376+00:00
-- url     : https://prove2.me/submissions/50030428-1ee6-4c5c-b2b9-b0ac2d76d5ed

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 81/320]`, `ρ ∈ [311/1280, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 210370560 203816960 206602240 ⟨⟨78385327673, 78385327679⟩, ⟨76443308035, 80342189111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 210370560 211025920 203816960 206602240 ⟨⟨78055159905, 78055159911⟩, ⟨76118459142, 80006640200⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 209715200 210370560 206602240 209387520 ⟨⟨79397607156, 79397607164⟩, ⟨77451405961, 81358652623⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 210370560 211025920 206602240 209387520 ⟨⟨79063573658, 79063573665⟩, ⟨77122701197, 81019228344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 211025920 211681280 203816960 206602240 ⟨⟨77726014923, 77726014925⟩, ⟨75794606953, 79672140574⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 211681280 212336640 203816960 206602240 ⟨⟨77397885040, 77397885046⟩, ⟨75471743988, 79338682341⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 211025920 211681280 206602240 209387520 ⟨⟨78730570376, 78730570379⟩, ⟨76795000580, 80680860759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 211681280 212336640 206602240 209387520 ⟨⟨78398589584, 78398589589⟩, ⟨76468296594, 80343541940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 209715200 210370560 209387520 212172800 ⟨⟨80408688960, 80408688967⟩, ⟨78458312951, 82373911618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 210370560 211025920 209387520 212172800 ⟨⟨80070803360, 80070803368⟩, ⟨78125765822, 82030625723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 209715200 210370560 212172800 214958080 ⟨⟨81418579659, 81418579667⟩, ⟨79464035541, 83387972716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 210370560 211025920 212172800 214958080 ⟨⟨81076855492, 81076855498⟩, ⟨79127659456, 83040838859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 211025920 211681280 209387520 212172800 ⟨⟨79733955276, 79733955279⟩, ⟨77794230154, 81688403800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 211681280 212336640 209387520 212172800 ⟨⟨79398136943, 79398136948⟩, ⟨77463698397, 81347237884⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 211025920 211681280 212172800 214958080 ⟨⟨80736176005, 80736176008⟩, ⟨78792302020, 82694776121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 211681280 212336640 212172800 214958080 ⟨⟨80396533406, 80396533413⟩, ⟨78457955646, 82349776505⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 212336640 203816960 214958080 t = true :=
  ⟨_, (join_sr (m := 209387520) (by decide) (join_su (m := 211025920) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 210370560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 210370560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 206602240) (by decide) (join_su (m := 211681280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 211681280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 211025920) (by decide) (join_sr (m := 212172800) (by decide) (join_su (m := 210370560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 210370560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 212172800) (by decide) (join_su (m := 211681280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 211681280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (81/320 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

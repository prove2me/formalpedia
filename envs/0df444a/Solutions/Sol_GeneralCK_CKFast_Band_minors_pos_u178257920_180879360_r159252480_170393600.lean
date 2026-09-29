-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_180879360_r159252480_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:30:07.170688+00:00
-- url     : https://prove2.me/submissions/226b7b20-2c84-4b98-a112-49f218067142

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 69/320]`, `ρ ∈ [243/1280, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 178913280 159252480 162037760 ⟨⟨76001837884, 76001837887⟩, ⟨73845196482, 78177076172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178913280 179568640 159252480 162037760 ⟨⟨75683325814, 75683325820⟩, ⟨73533388211, 77851765490⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 178257920 178913280 162037760 164823040 ⟨⟨77243530548, 77243530550⟩, ⟨75082019515, 79423627643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 178913280 179568640 162037760 164823040 ⟨⟨76920379684, 76920379690⟩, ⟨74765584104, 79093666950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 179568640 180224000 159252480 162037760 ⟨⟨75366126766, 75366126772⟩, ⟨73222853083, 77527808477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 180224000 180879360 159252480 162037760 ⟨⟨75050229451, 75050229458⟩, ⟨72913580187, 77205193462⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 179568640 180224000 162037760 164823040 ⟨⟨76598554757, 76598554763⟩, ⟨74450434782, 78765072804⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 180224000 180879360 162037760 164823040 ⟨⟨76278044405, 76278044412⟩, ⟨74136560560, 78437833464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 178257920 178913280 164823040 167608320 ⟨⟨78482966557, 78482966560⟩, ⟨76316602543, 80667905673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 178913280 179568640 164823040 167608320 ⟨⟨78155201724, 78155201731⟩, ⟨75995564567, 80333320043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 178257920 178913280 167608320 170393600 ⟨⟨79720160807, 79720160810⟩, ⟨77548960317, 81909925293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 178913280 179568640 167608320 170393600 ⟨⟨79387806607, 79387806614⟩, ⟨77223344131, 81570739577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 179568640 180224000 164823040 167608320 ⟨⟨77828775495, 77828775502⟩, ⟨75675825378, 80000113589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 180224000 180879360 164823040 167608320 ⟨⟨77503676432, 77503676438⟩, ⟨75357373912, 79668274494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 179568640 180224000 167608320 170393600 ⟨⟨79056803429, 79056803436⟩, ⟨76899039187, 81232945413⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 180224000 180879360 167608320 170393600 ⟨⟨78727139765, 78727139773⟩, ⟨76576034346, 80896530916⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 180879360 159252480 170393600 t = true :=
  ⟨_, (join_sr (m := 164823040) (by decide) (join_su (m := 179568640) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 178913280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 178913280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 162037760) (by decide) (join_su (m := 180224000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 180224000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 179568640) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 178913280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 178913280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 167608320) (by decide) (join_su (m := 180224000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 180224000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (69/320 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((180879360 : ℤ) : ℝ) / (D : ℝ)) = (69/320 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

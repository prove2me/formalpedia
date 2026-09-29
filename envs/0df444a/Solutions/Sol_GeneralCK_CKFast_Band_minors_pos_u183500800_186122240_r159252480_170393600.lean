-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u183500800_186122240_r159252480_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:37:13.579094+00:00
-- url     : https://prove2.me/submissions/4870ae61-abbe-489e-bf41-2a84dede8580

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/32, 71/320]`, `ρ ∈ [243/1280, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 183500800 184156160 159252480 162037760 ⟨⟨73489882399, 73489882405⟩, ⟨71385775487, 75611848834⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 184156160 184811520 159252480 162037760 ⟨⟨73181565260, 73181565266⟩, ⟨71083853362, 75297047816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 183500800 184156160 162037760 164823040 ⟨⟨74694822154, 74694822161⟩, ⟨72585939587, 76821556725⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 184156160 184811520 162037760 164823040 ⟨⟨74381967455, 74381967461⟩, ⟨72279491755, 76502206679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 184811520 185466880 159252480 162037760 ⟨⟨72874474211, 72874474214⟩, ⟨70783120317, 74983510600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 185466880 186122240 159252480 162037760 ⟨⟨72568598899, 72568598905⟩, ⟨70483566343, 74671226495⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 184811520 185466880 162037760 164823040 ⟨⟨74070351169, 74070351170⟩, ⟨71974245342, 76184132733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 185466880 186122240 162037760 164823040 ⟨⟨73759962867, 73759962873⟩, ⟨71670190269, 75867324122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 183500800 184156160 164823040 167608320 ⟨⟨75897696985, 75897696993⟩, ⟨73784053494, 78029184831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 184156160 184811520 164823040 167608320 ⟨⟨75580327619, 75580327625⟩, ⟨73473102615, 77705308878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 183500800 184156160 167608320 170393600 ⟨⟨77098520088, 77098520096⟩, ⟨74980130280, 79234746463⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 184156160 184811520 167608320 170393600 ⟨⟨76776658746, 76776658754⟩, ⟨74664698827, 78906367522⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 184811520 185466880 164823040 167608320 ⟨⟨75264208754, 75264208757⟩, ⟨73163365272, 77382721088⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 185466880 186122240 164823040 167608320 ⟨⟨74949329897, 74949329904⟩, ⟨72854831309, 77061410629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 184811520 185466880 167608320 170393600 ⟨⟨76456059770, 76456059775⟩, ⟨74350492795, 78579288578⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 185466880 186122240 167608320 170393600 ⟨⟨76136712598, 76136712606⟩, ⟨74037501963, 78253498729⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 183500800 186122240 159252480 170393600 t = true :=
  ⟨_, (join_sr (m := 164823040) (by decide) (join_su (m := 184811520) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 184156160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 184156160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 162037760) (by decide) (join_su (m := 185466880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 185466880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 184811520) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 184156160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 184156160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 167608320) (by decide) (join_su (m := 185466880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 185466880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/32 : ℝ) (71/320 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e1 : (((186122240 : ℤ) : ℝ) / (D : ℝ)) = (71/320 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

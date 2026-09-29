-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_188743680_r437780480_460062720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:04:20.739308+00:00
-- url     : https://prove2.me/submissions/b8017482-1219-4726-938b-4edfa69ee033

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 9/40]`, `ρ ∈ [167/320, 351/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 180879360 437780480 443351040 ⟨⟨190550008004, 190550008013⟩, ⟨181989993850, 199297273635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178257920 180879360 443351040 448921600 ⟨⟨192689673590, 192689673599⟩, ⟨184101465793, 201464808456⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 180879360 183500800 437780480 443351040 ⟨⟨187811497880, 187811497889⟩, ⟨179331775707, 196476661673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 180879360 183500800 443351040 448921600 ⟨⟨189927391274, 189927391283⟩, ⟨181419423442, 198620511751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 178257920 180879360 448921600 454492160 ⟨⟨194824754066, 194824754075⟩, ⟨186208442054, 203627663324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 178257920 180879360 454492160 460062720 ⟨⟨196955310309, 196955310318⟩, ⟨188310982140, 205785900496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 180879360 183500800 448921600 454492160 ⟨⟨192038861228, 192038861236⟩, ⟨183502732893, 200759847839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 180879360 183500800 454492160 460062720 ⟨⟨194145965899, 194145965908⟩, ⟨185581760931, 202894729391⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 183500800 186122240 437780480 443351040 ⟨⟨185100364791, 185100364800⟩, ⟨176699595588, 193684793843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 183500800 186122240 443351040 448921600 ⟨⟨187192453915, 187192453923⟩, ⟨178763400695, 195804912076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 186122240 188743680 437780480 443351040 ⟨⟨182415905494, 182415905503⟩, ⟨174092785167, 190920931540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 186122240 188743680 443351040 448921600 ⟨⟨184484162236, 184484162243⟩, ⟨176132732582, 193017275455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 183500800 186122240 448921600 454492160 ⟨⟨189280277116, 189280277125⟩, ⟨180823020827, 197920678082⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 183500800 186122240 454492160 460062720 ⟨⟨191363889941, 191363889951⟩, ⟨182878510325, 200032148624⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 186122240 188743680 448921600 454492160 ⟨⟨186548306483, 186548306492⟩, ⟨178168644310, 195109424763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 186122240 188743680 454492160 460062720 ⟨⟨188608391278, 188608391287⟩, ⟨180200572261, 197197433640⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 188743680 437780480 460062720 t = true :=
  ⟨_, (join_su (m := 183500800) (by decide) (join_sr (m := 448921600) (by decide) (join_su (m := 180879360) (by decide) (join_sr (m := 443351040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 443351040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 180879360) (by decide) (join_sr (m := 454492160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 454492160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 448921600) (by decide) (join_su (m := 186122240) (by decide) (join_sr (m := 443351040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 443351040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 186122240) (by decide) (join_sr (m := 454492160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 454492160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (167/320 : ℝ) (351/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  have e3 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

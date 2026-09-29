-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u153354240_154664960_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:01:40.704588+00:00
-- url     : https://prove2.me/submissions/9a499557-2480-4e4e-badc-0bfcb1ecb0e0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [117/640, 59/320]`, `ρ ∈ [1/10, 137/1280]` by 14 cells of the computing
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
theorem cell0 : cellOK 153354240 153681920 83886080 85360640 ⟨⟨48847960476, 48847960482⟩, ⟨47673240653, 50028900675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 153681920 154009600 83886080 85360640 ⟨⟨48737289141, 48737289148⟩, ⟨47564683903, 49916094320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 153354240 153681920 85360640 86835200 ⟨⟨49660833761, 49660833769⟩, ⟨48484449677, 50843434036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 153681920 154009600 85360640 86835200 ⟨⟨49548469801, 49548469809⟩, ⟨48374203350, 50728932065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 154009600 154337280 83886080 85360640 ⟨⟨48626930798, 48626930806⟩, ⟨47456432403, 49803608806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 154337280 154664960 83886080 85360640 ⟨⟨48516883789, 48516883796⟩, ⟨47348484538, 49691442430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 154009600 154337280 85360640 86835200 ⟨⟨49436422760, 49436422768⟩, ⟨48264266196, 50614754864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 154337280 154664960 85360640 86835200 ⟨⟨49324690961, 49324690968⟩, ⟨48154636583, 50500900714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 153354240 153681920 86835200 88309760 ⟨⟨50472507983, 50472507989⟩, ⟨49294465285, 51656762669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 153681920 154009600 86835200 88309760 ⟨⟨50358458487, 50358458493⟩, ⟨49182536428, 51540572215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 153354240 154009600 88309760 89784320 ⟨⟨51225083676, 51225083684⟩, ⟨49345912485, 53119866591⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 154009600 154337280 86835200 88309760 ⟨⟨50244729795, 50244729801⟩, ⟨49070920622, 51424710420⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 154337280 154664960 86835200 88309760 ⟨⟨50131320211, 50131320218⟩, ⟨48959616221, 51309175545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 154009600 154664960 88309760 89784320 ⟨⟨50994276571, 50994276577⟩, ⟨49121154838, 52882917285⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 153354240 154664960 83886080 89784320 t = true :=
  ⟨_, (join_sr (m := 86835200) (by decide) (join_su (m := 154009600) (by decide) (join_sr (m := 85360640) (by decide) (join_su (m := 153681920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 153681920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 85360640) (by decide) (join_su (m := 154337280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 154337280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 154009600) (by decide) (join_sr (m := 88309760) (by decide) (join_su (m := 153681920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 88309760) (by decide) (join_su (m := 154337280) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (117/640 : ℝ) (59/320 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((153354240 : ℤ) : ℝ) / (D : ℝ)) = (117/640 : ℝ) := by norm_num [D]
  have e1 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_228065280_r148111360_153681920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:14:30.495977+00:00
-- url     : https://prove2.me/submissions/a4f2cce5-a859-47e3-b7e4-78e69ea9405c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 87/320]`, `ρ ∈ [113/640, 469/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226099200 148111360 149504000 ⟨⟨51866685862, 51866685868⟩, ⟨50395344833, 53347211002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 225443840 226099200 149504000 150896640 ⟨⟨52337218336, 52337218341⟩, ⟨50864028706, 53819597177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 226099200 226754560 148111360 149504000 ⟨⟨51636384465, 51636384470⟩, ⟨50168240525, 53113679451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226099200 226754560 149504000 150896640 ⟨⟨52104949543, 52104949550⟩, ⟨50634961991, 53584093283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 225443840 226099200 150896640 152289280 ⟨⟨52807499676, 52807499681⟩, ⟨51332462233, 54291731418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 225443840 226099200 152289280 153681920 ⟨⟨53277530516, 53277530522⟩, ⟨51800646047, 54763614357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 226099200 226754560 150896640 152289280 ⟨⟨52573266576, 52573266582⟩, ⟨51101436178, 54054258286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 226099200 226754560 152289280 153681920 ⟨⟨53041336184, 53041336189⟩, ⟨51567663705, 54524175085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 226754560 227409920 148111360 149504000 ⟨⟨51406781297, 51406781304⟩, ⟨49941818162, 52880862649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 226754560 227409920 149504000 150896640 ⟨⟨51873383465, 51873383472⟩, ⟨50406581694, 53349308625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 227409920 228065280 148111360 149504000 ⟨⟨51177871027, 51177871030⟩, ⟨49716072528, 52648755129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 227409920 228065280 149504000 150896640 ⟨⟨51642514737, 51642514740⟩, ⟨50178882572, 53115237714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 226754560 227409920 150896640 152289280 ⟨⟨52339740640, 52339740645⟩, ⟨50871100981, 53817508849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 226754560 227409920 152289280 153681920 ⟨⟨52805853434, 52805853439⟩, ⟨51335376631, 54285463934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 227409920 228065280 150896640 152289280 ⟨⟨52106916475, 52106916478⟩, ⟨50641451371, 53581477590⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 227409920 228065280 152289280 153681920 ⟨⟨52571076846, 52571076848⟩, ⟨51103779529, 54047475358⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 228065280 148111360 153681920 t = true :=
  ⟨_, (join_su (m := 226754560) (by decide) (join_sr (m := 150896640) (by decide) (join_su (m := 226099200) (by decide) (join_sr (m := 149504000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 149504000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 226099200) (by decide) (join_sr (m := 152289280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 152289280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 150896640) (by decide) (join_su (m := 227409920) (by decide) (join_sr (m := 149504000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 149504000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 227409920) (by decide) (join_sr (m := 152289280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 152289280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (87/320 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

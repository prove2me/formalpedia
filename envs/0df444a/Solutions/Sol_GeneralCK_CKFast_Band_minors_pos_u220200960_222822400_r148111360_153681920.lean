-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_222822400_r148111360_153681920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:01:04.978984+00:00
-- url     : https://prove2.me/submissions/45c7a566-9f8d-4cad-ba40-9099183f1170

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 17/64]`, `ρ ∈ [113/640, 469/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 220856320 148111360 149504000 ⟨⟨53734889851, 53734889858⟩, ⟨52237370307, 55241866443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 220856320 149504000 150896640 ⟨⟨54221326249, 54221326256⟩, ⟨52721917875, 55730196450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 220856320 221511680 148111360 149504000 ⟨⟨53498804622, 53498804625⟩, ⟨52004617127, 55002414203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 220856320 221511680 149504000 150896640 ⟨⟨53983236740, 53983236743⟩, ⟨52487165474, 55488734912⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 220856320 150896640 152289280 ⟨⟨54707485643, 54707485649⟩, ⟨53206189405, 56218248473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 220856320 152289280 153681920 ⟨⟨55193368750, 55193368756⟩, ⟨53690185610, 56706023230⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 220856320 221511680 150896640 152289280 ⟨⟨54467395205, 54467395207⟩, ⟨52969441112, 55974781012⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 220856320 221511680 152289280 153681920 ⟨⟨54951280725, 54951280726⟩, ⟨53451444744, 56460553212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 221511680 222167040 148111360 149504000 ⟨⟨53263462083, 53263462088⟩, ⟨51772589304, 54763722236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 221511680 222167040 149504000 150896640 ⟨⟨53745894632, 53745894638⟩, ⟨52253143134, 55248038368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 222167040 222822400 148111360 149504000 ⟨⟨53028856503, 53028856509⟩, ⟨51541281239, 54525784671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 222167040 222822400 149504000 150896640 ⟨⟨53509294168, 53509294174⟩, ⟨52019845229, 55008100917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 221511680 222167040 150896640 152289280 ⟨⟨54228056847, 54228056853⟩, ⟨52733427551, 55732083232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 221511680 222167040 152289280 153681920 ⟨⟨54709949424, 54709949429⟩, ⟨53213443244, 56215857526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 222167040 222822400 150896640 152289280 ⟨⟨53989464782, 53989464788⟩, ⟨52498143062, 55490149202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 222167040 222822400 152289280 153681920 ⟨⟨54469369031, 54469369036⟩, ⟨52976175424, 55971930212⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 222822400 148111360 153681920 t = true :=
  ⟨_, (join_su (m := 221511680) (by decide) (join_sr (m := 150896640) (by decide) (join_su (m := 220856320) (by decide) (join_sr (m := 149504000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 149504000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 220856320) (by decide) (join_sr (m := 152289280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 152289280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 150896640) (by decide) (join_su (m := 222167040) (by decide) (join_sr (m := 149504000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 149504000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 222167040) (by decide) (join_sr (m := 152289280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 152289280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (17/64 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_221511680_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:41:27.07803+00:00
-- url     : https://prove2.me/submissions/1215f292-02e1-4d47-93bc-784e070e5f12

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 169/640]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 220528640 125829120 127221760 ⟨⟨45964633758, 45964633760⟩, ⟨45090276998, 46842419924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220528640 220856320 125829120 127221760 ⟨⟨45862691490, 45862691495⟩, ⟨44989490413, 46739314383⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 220200960 220528640 127221760 128614400 ⟨⟨46456117098, 46456117101⟩, ⟨45580715026, 47334949554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 220528640 220856320 127221760 128614400 ⟨⟨46353143763, 46353143768⟩, ⟨45478899031, 47230811298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220856320 221184000 125829120 127221760 ⟨⟨45760915821, 45760915828⟩, ⟨44888867568, 46636378326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 221184000 221511680 125829120 127221760 ⟨⟨45659306095, 45659306100⟩, ⟨44788407810, 46533611091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 220856320 221184000 127221760 128614400 ⟨⟨46250338356, 46250338362⟩, ⟨45377248101, 47126843859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 221184000 221511680 127221760 128614400 ⟨⟨46147700215, 46147700221⟩, ⟨45275761582, 47023046566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 220200960 220528640 128614400 130007040 ⟨⟨46947310800, 46947310803⟩, ⟨46070864155, 47827188805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 220528640 220856320 128614400 130007040 ⟨⟨46843308177, 46843308182⟩, ⟨45968020519, 47722019621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 220200960 220528640 130007040 131399680 ⟨⟨47438215617, 47438215620⟩, ⟨46560725133, 48319138431⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 220528640 220856320 130007040 131399680 ⟨⟨47333185475, 47333185482⟩, ⟨46456855620, 48212940099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 220856320 221184000 128614400 130007040 ⟨⟨46739474800, 46739474805⟩, ⟨45865343266, 47617022574⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 221184000 221511680 128614400 130007040 ⟨⟨46635810004, 46635810010⟩, ⟨45762831736, 47512196992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 220856320 221184000 130007040 131399680 ⟨⟨47228325893, 47228325898⟩, ⟨46353153799, 48106915216⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 221184000 221511680 130007040 131399680 ⟨⟨47123636196, 47123636201⟩, ⟨46249619004, 48001063103⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 221511680 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 220856320) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 220528640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 220528640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 221184000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 221184000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 220856320) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 220528640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 220528640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 221184000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 221184000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (169/640 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((221511680 : ℤ) : ℝ) / (D : ℝ)) = (169/640 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

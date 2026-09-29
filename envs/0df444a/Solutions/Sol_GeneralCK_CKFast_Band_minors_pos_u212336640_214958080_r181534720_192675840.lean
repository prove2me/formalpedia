-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u212336640_214958080_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:21:22.528507+00:00
-- url     : https://prove2.me/submissions/1b5200ec-41e0-455e-b812-f70ad1439540

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [81/320, 41/160]`, `ρ ∈ [277/1280, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 212336640 212992000 181534720 184320000 ⟨⟨69053938357, 69053938364⟩, ⟨67166404959, 70956037158⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 212992000 213647360 181534720 184320000 ⟨⟨68758989101, 68758989107⟩, ⟨66876587792, 70655893568⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212336640 212992000 184320000 187105280 ⟨⟨70060177912, 70060177919⟩, ⟨68168450965, 71966474303⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212992000 213647360 184320000 187105280 ⟨⟨69761284132, 69761284137⟩, ⟨67874700164, 71662375498⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 213647360 214302720 181534720 184320000 ⟨⟨68464969363, 68464969370⟩, ⟨66587674819, 70356705253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 214302720 214958080 181534720 184320000 ⟨⟨68171872063, 68171872067⟩, ⟨66299659156, 70058464923⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 213647360 214302720 184320000 187105280 ⟨⟨69463328205, 69463328211⟩, ⟨67581861893, 71359240297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 214302720 214958080 184320000 187105280 ⟨⟨69166303005, 69166303009⟩, ⟨67289929223, 71057061366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 212336640 212992000 187105280 189890560 ⟨⟨71065222766, 71065222772⟩, ⟨69169308848, 72975710076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 212992000 213647360 187105280 189890560 ⟨⟨70762398330, 70762398337⟩, ⟨68871638160, 72667670051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 212336640 212992000 189890560 192675840 ⟨⟨72069079379, 72069079384⟩, ⟨70168985031, 73983750978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 212992000 213647360 189890560 192675840 ⟨⟨71762338064, 71762338069⟩, ⟨69867408104, 73671783634⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 213647360 214302720 187105280 189890560 ⟨⟨70460519949, 70460519956⟩, ⟨68574888204, 72360601824⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 214302720 214958080 187105280 189890560 ⟨⟨70159580448, 70159580453⟩, ⟨68279052004, 72054498015⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 213647360 214302720 189890560 192675840 ⟨⟨71456550866, 71456550871⟩, ⟨69566759978, 73360796142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 214302720 214958080 189890560 192675840 ⟨⟨71151710570, 71151710572⟩, ⟨69267033633, 73050781082⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 212336640 214958080 181534720 192675840 t = true :=
  ⟨_, (join_sr (m := 187105280) (by decide) (join_su (m := 213647360) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 212992000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 212992000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184320000) (by decide) (join_su (m := 214302720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 214302720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 213647360) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 212992000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 212992000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 189890560) (by decide) (join_su (m := 214302720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 214302720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (81/320 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

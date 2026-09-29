-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u231997440_233308160_r148111360_153681920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:51:51.755504+00:00
-- url     : https://prove2.me/submissions/8336d691-8581-47a6-a8c1-a110f3462552

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [177/640, 89/320]`, `ρ ∈ [113/640, 469/2560]` by 12 cells of the computing
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
theorem cell0 : cellOK 231997440 232325120 148111360 149504000 ⟨⟨49650451633, 49650451638⟩, ⟨48800240196, 50503855134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 232325120 232652800 148111360 149504000 ⟨⟨49538512187, 49538512192⟩, ⟨48689384800, 50390825058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231997440 232325120 149504000 150896640 ⟨⟨50101990132, 50101990137⟩, ⟨49250799256, 50956374273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 232325120 232652800 149504000 150896640 ⟨⟨49989087720, 49989087725⟩, ⟨49138982378, 50842379755⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 232652800 232980480 148111360 149504000 ⟨⟨49426735390, 49426735397⟩, ⟨48578689541, 50277960165⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 232980480 233308160 148111360 149504000 ⟨⟨49315120628, 49315120634⟩, ⟨48468153813, 50165259832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 232652800 232980480 149504000 150896640 ⟨⟨49876349014, 49876349021⟩, ⟨49027326690, 50728551479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 232980480 233308160 149504000 150896640 ⟨⟨49763773396, 49763773402⟩, ⟨48915831586, 50614888818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 231997440 232652800 150896640 152289280 ⟨⟨50496353631, 50496353638⟩, ⟨49052667573, 51948914052⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231997440 232652800 152289280 153681920 ⟨⟨50946967705, 50946967710⟩, ⟨49501483686, 52401331507⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 232652800 233308160 150896640 152289280 ⟨⟨50268955027, 50268955034⟩, ⟨48828318417, 51718435183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 232652800 233308160 152289280 153681920 ⟨⟨50717650832, 50717650837⟩, ⟨49275221121, 52168929543⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 231997440 233308160 148111360 153681920 t = true :=
  ⟨_, (join_sr (m := 150896640) (by decide) (join_su (m := 232652800) (by decide) (join_sr (m := 149504000) (by decide) (join_su (m := 232325120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 232325120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 149504000) (by decide) (join_su (m := 232980480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 232980480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 232652800) (by decide) (join_sr (m := 152289280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 152289280) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (177/640 : ℝ) (89/320 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((231997440 : ℤ) : ℝ) / (D : ℝ)) = (177/640 : ℝ) := by norm_num [D]
  have e1 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

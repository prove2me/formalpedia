-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_178257920_r571473920_616038400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:04:29.002844+00:00
-- url     : https://prove2.me/submissions/d9446581-52e1-47d8-a4c2-d0515c345fa9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 17/80]`, `ρ ∈ [109/160, 47/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 170393600 571473920 582615040 ⟨⟨255164012364, 255164012374⟩, ⟨243836444056, 266749878346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 170393600 173015040 571473920 582615040 ⟨⟨251775514961, 251775514971⟩, ⟨240559726625, 263247822830⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 167772160 170393600 582615040 593756160 ⟨⟨259409199232, 259409199242⟩, ⟨248028027889, 271046556205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 170393600 173015040 582615040 593756160 ⟨⟨255980758649, 255980758659⟩, ⟨244710862376, 267505184641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 173015040 175636480 571473920 582615040 ⟨⟨248415173391, 248415173401⟩, ⟨237309722283, 259775360772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 175636480 178257920 571473920 582615040 ⟨⟨245082320592, 245082320597⟩, ⟨234085794662, 256331795506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 173015040 175636480 582615040 593756160 ⟨⟨252580214500, 252580214508⟩, ⟨241420192309, 263993101609⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 175636480 178257920 582615040 593756160 ⟨⟨249206910736, 249206910739⟩, ⟨238155390859, 260509623036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 167772160 170393600 593756160 604897280 ⟨⟨263639802445, 263639802455⟩, ⟨252205368435, 275328289025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 170393600 173015040 593756160 604897280 ⟨⟨260171866962, 260171866973⟩, ⟨248848191995, 271748060187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 167772160 170393600 604897280 616038400 ⟨⟨267856264017, 267856264027⟩, ⟨256368895146, 279595531261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 170393600 173015040 604897280 616038400 ⟨⟨264349265131, 264349265141⟩, ⟨252972128709, 275976886587⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 173015040 175636480 593756160 604897280 ⟨⟨256731560253, 256731560263⟩, ⟨245517284899, 268196806997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 175636480 178257920 593756160 604897280 ⟨⟨253318237237, 253318237242⟩, ⟨242212029846, 264673857879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 173015040 175636480 604897280 616038400 ⟨⟨260869619598, 260869619608⟩, ⟨249601397541, 272386897234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 175636480 178257920 604897280 616038400 ⟨⟨257416693255, 257416693261⟩, ⟨246256093856, 268824904020⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 178257920 571473920 616038400 t = true :=
  ⟨_, (join_sr (m := 593756160) (by decide) (join_su (m := 173015040) (by decide) (join_sr (m := 582615040) (by decide) (join_su (m := 170393600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 170393600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 582615040) (by decide) (join_su (m := 175636480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 175636480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 173015040) (by decide) (join_sr (m := 604897280) (by decide) (join_su (m := 170393600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 170393600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 604897280) (by decide) (join_su (m := 175636480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 175636480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (109/160 : ℝ) (47/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((571473920 : ℤ) : ℝ) / (D : ℝ)) = (109/160 : ℝ) := by norm_num [D]
  have e3 : (((616038400 : ℤ) : ℝ) / (D : ℝ)) = (47/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

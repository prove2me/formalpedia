-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_136314880_r390594560_414187520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:46:48.288975+00:00
-- url     : https://prove2.me/submissions/8808d706-c47c-4790-8164-e1318b4d24bd

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 13/80]`, `ρ ∈ [149/320, 79/160]` by 14 cells of the computing
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
theorem cell0 : cellOK 125829120 128450560 390594560 396492800 ⟨⟨230080876362, 230080876374⟩, ⟨219632229513, 240778131221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 125829120 128450560 396492800 402391040 ⟨⟨232917668602, 232917668613⟩, ⟨222442902688, 243639480069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 128450560 131072000 390594560 396492800 ⟨⟨226797795638, 226797795648⟩, ⟨216472697055, 237368247376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 128450560 131072000 396492800 402391040 ⟨⟨229609015829, 229609015838⟩, ⟨219257278905, 240204635366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 125829120 128450560 402391040 414187520 ⟨⟨237151746848, 237151746859⟩, ⟨224194593308, 250481444179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 128450560 131072000 402391040 414187520 ⟨⟨233805380380, 233805380391⟩, ⟨221014100368, 246963968195⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 131072000 133693440 390594560 396492800 ⟨⟨223564104234, 223564104245⟩, ⟨213359789216, 234010582728⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 131072000 133693440 396492800 402391040 ⟨⟨226349600789, 226349600800⟩, ⟨216118168218, 236821814177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 133693440 136314880 390594560 396492800 ⟨⟨220378246195, 220378246205⟩, ⟨210292044670, 230703485411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 133693440 136314880 396492800 402391040 ⟨⟨223137881764, 223137881775⟩, ⟨213024121396, 233489381207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 131072000 133693440 402391040 408289280 ⟨⟨229124488382, 229124488393⟩, ⟨218866166427, 239622206688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 131072000 133693440 408289280 414187520 ⟨⟨231888947524, 231888947532⟩, ⟨221603959112, 242411946055⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 133693440 136314880 402391040 408289280 ⟨⟨225887238517, 225887238526⟩, ⟨215746141507, 236264773499⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 133693440 136314880 408289280 414187520 ⟨⟨228626489170, 228626489179⟩, ⟨218458272735, 239029840030⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 136314880 390594560 414187520 t = true :=
  ⟨_, (join_su (m := 131072000) (by decide) (join_sr (m := 402391040) (by decide) (join_su (m := 128450560) (by decide) (join_sr (m := 396492800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 396492800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 128450560) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 402391040) (by decide) (join_su (m := 133693440) (by decide) (join_sr (m := 396492800) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 396492800) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 133693440) (by decide) (join_sr (m := 408289280) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 408289280) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (149/320 : ℝ) (79/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((390594560 : ℤ) : ℝ) / (D : ℝ)) = (149/320 : ℝ) := by norm_num [D]
  have e3 : (((414187520 : ℤ) : ℝ) / (D : ℝ)) = (79/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

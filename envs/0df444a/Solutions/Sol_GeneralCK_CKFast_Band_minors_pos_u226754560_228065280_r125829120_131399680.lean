-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u226754560_228065280_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:50:07.256998+00:00
-- url     : https://prove2.me/submissions/693ea4ba-7f44-44dc-833c-cd1c0721eef8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [173/640, 87/320]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 226754560 227082240 125829120 127221760 ⟨⟨43956706761, 43956706765⟩, ⟨43104932703, 44811763392⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 227082240 227409920 125829120 127221760 ⟨⟨43857974874, 43857974880⟩, ⟨43007301381, 44711923869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 226754560 227082240 127221760 128614400 ⟨⟨44427816223, 44427816226⟩, ⟨43575029575, 45283886591⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 227082240 227409920 127221760 128614400 ⟨⟨44328079016, 44328079023⟩, ⟨43476394549, 45183040143⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 227409920 227737600 125829120 127221760 ⟨⟨43759396991, 43759396997⟩, ⟨42909821423, 44612241012⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 227737600 228065280 125829120 127221760 ⟨⟨43660972510, 43660972516⟩, ⟨42812492234, 44512714216⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 227409920 227737600 127221760 128614400 ⟨⟨44228497057, 44228497063⟩, ⟨43377912125, 45082351606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 227737600 228065280 127221760 128614400 ⟨⟨44129069738, 44129069744⟩, ⟨43279581707, 44981820370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 226754560 227082240 128614400 130007040 ⟨⟨44898669879, 44898669883⟩, ⟨44044871231, 45755753392⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 227082240 227409920 128614400 130007040 ⟨⟨44797928953, 44797928959⟩, ⟨43945234091, 45653901624⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 226754560 227082240 130007040 131399680 ⟨⟨45369268370, 45369268374⟩, ⟨44514458309, 46227364436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 227082240 227409920 130007040 131399680 ⟨⟨45267525318, 45267525323⟩, ⟨44413820643, 46124508951⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 227409920 227737600 128614400 130007040 ⟨⟨44697344508, 44697344513⟩, ⟨43845750787, 45552209006⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 227737600 228065280 128614400 130007040 ⟨⟨44596915933, 44596915939⟩, ⟨43746420716, 45450674919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 227409920 227737600 130007040 131399680 ⟨⟨45165939973, 45165939978⟩, ⟨44313338036, 46021813840⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 227737600 228065280 130007040 131399680 ⟨⟨45064511719, 45064511726⟩, ⟨44213009883, 45919278488⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 226754560 228065280 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 227409920) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 227082240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 227082240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 227737600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 227737600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 227409920) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 227082240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 227082240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 227737600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 227737600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (173/640 : ℝ) (87/320 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((226754560 : ℤ) : ℝ) / (D : ℝ)) = (173/640 : ℝ) := by norm_num [D]
  have e1 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

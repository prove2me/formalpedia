-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u183500800_188743680_r326369280_348651520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:46:49.528536+00:00
-- url     : https://prove2.me/submissions/dfa86094-2ab2-4eba-8cd3-002977bb6e2f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/32, 9/40]`, `ρ ∈ [249/640, 133/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 183500800 184811520 326369280 331939840 ⟨⟨142818656606, 142818656614⟩, ⟨138102234950, 147603689826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 184811520 186122240 326369280 331939840 ⟨⟨141726486389, 141726486398⟩, ⟨137036916099, 146484154780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 183500800 184811520 331939840 337510400 ⟨⟨145015577829, 145015577838⟩, ⟨140282897467, 149816754648⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 184811520 186122240 331939840 337510400 ⟨⟨143909641003, 143909641012⟩, ⟨139203827730, 148683443777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 186122240 187432960 326369280 331939840 ⟨⟨140640817950, 140640817954⟩, ⟨135977844353, 145371382000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 187432960 188743680 326369280 331939840 ⟨⟨139561559252, 139561559259⟩, ⟨134924931482, 144265275571⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 186122240 187432960 331939840 337510400 ⟨⟨142810225937, 142810225941⟩, ⟨138131026872, 147556913206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 187432960 188743680 331939840 337510400 ⟨⟨141717240780, 141717240787⟩, ⟨137064406791, 146437067264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 183500800 184811520 337510400 343080960 ⟨⟨147206932801, 147206932809⟩, ⟨142458065898, 152024179437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 184811520 186122240 337510400 343080960 ⟨⟨146087337463, 146087337471⟩, ⟨141365351505, 150877202710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 183500800 184811520 343080960 348651520 ⟨⟨149392791582, 149392791589⟩, ⟨144627809202, 154226035360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 184811520 186122240 343080960 348651520 ⟨⟨148259644061, 148259644070⟩, ⟨143521554655, 153065500941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 186122240 187432960 337510400 343080960 ⟨⟨144974282189, 144974282193⟩, ⟨140278926111, 149737022615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 187432960 188743680 337510400 343080960 ⟨⟨143867675334, 143867675342⟩, ⟨139198701768, 148603543742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 186122240 187432960 343080960 348651520 ⟨⟨147133053272, 147133053276⟩, ⟨142421607612, 151911777823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 187432960 188743680 343080960 348651520 ⟨⟨146012927796, 146012927805⟩, ⟨141327880303, 150764770882⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 183500800 188743680 326369280 348651520 t = true :=
  ⟨_, (join_sr (m := 337510400) (by decide) (join_su (m := 186122240) (by decide) (join_sr (m := 331939840) (by decide) (join_su (m := 184811520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 184811520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 331939840) (by decide) (join_su (m := 187432960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 187432960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 186122240) (by decide) (join_sr (m := 343080960) (by decide) (join_su (m := 184811520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 184811520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 343080960) (by decide) (join_su (m := 187432960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 187432960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/32 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (249/640 : ℝ) (133/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  have e3 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

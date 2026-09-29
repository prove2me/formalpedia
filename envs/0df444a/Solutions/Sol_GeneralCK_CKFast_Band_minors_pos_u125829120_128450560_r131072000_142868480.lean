-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_128450560_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:24:10.251774+00:00
-- url     : https://prove2.me/submissions/39e3dec0-36f0-44f1-b030-ac88d0cbc450

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 49/320]`, `ρ ∈ [5/32, 109/640]` by 14 cells of the computing
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
theorem cell0 : cellOK 125829120 126484480 131072000 134021120 ⟨⟨89956172896, 89956172900⟩, ⟨87081014082, 92863404324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 126484480 127139840 131072000 134021120 ⟨⟨89544001468, 89544001477⟩, ⟨86680873254, 92438972293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 125829120 126484480 134021120 136970240 ⟨⟨91776188419, 91776188425⟩, ⟨88894552161, 94689802589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 126484480 127139840 134021120 136970240 ⟨⟨91357061115, 91357061124⟩, ⟨88487463020, 94258409072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 127139840 127795200 131072000 134021120 ⟨⟨89134444793, 89134444800⟩, ⟨86283246258, 92017258535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 127795200 128450560 131072000 134021120 ⟨⟨88727472956, 88727472965⟩, ⟨85888104485, 91598231795⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 127139840 127795200 134021120 136970240 ⟨⟨90940577026, 90940577034⟩, ⟨88082916473, 93829761957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 127795200 128450560 134021120 136970240 ⟨⟨90526706052, 90526706061⟩, ⟨87680883720, 93403829807⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 125829120 126484480 136970240 139919360 ⟨⟨93589578172, 93589578174⟩, ⟨90701530527, 96509508945⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 126484480 127139840 136970240 139919360 ⟨⟨93163569071, 93163569079⟩, ⟨90287566266, 96071228906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 125829120 127139840 139919360 142868480 ⟨⟨95179662294, 95179662303⟩, ⟨90626691485, 99811594146⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 127139840 127795200 136970240 139919360 ⟨⟨92740230784, 92740230792⟩, ⟨89876172508, 95635722518⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 127795200 128450560 136970240 139919360 ⟨⟨92319533039, 92319533046⟩, ⟨89467320271, 95202958185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 127139840 128450560 139919360 142868480 ⟨⟨94319413961, 94319413965⟩, ⟨89801029076, 98915734030⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 128450560 131072000 142868480 t = true :=
  ⟨_, (join_sr (m := 136970240) (by decide) (join_su (m := 127139840) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 126484480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 126484480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 134021120) (by decide) (join_su (m := 127795200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 127795200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 127139840) (by decide) (join_sr (m := 139919360) (by decide) (join_su (m := 126484480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 139919360) (by decide) (join_su (m := 127795200) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (49/320 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((128450560 : ℤ) : ℝ) / (D : ℝ)) = (49/320 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

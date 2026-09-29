-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u183500800_188743680_r281804800_304087040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:46:47.894065+00:00
-- url     : https://prove2.me/submissions/9a93fda0-90a3-4a70-aec1-0ccd68efeff3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/32, 9/40]`, `ρ ∈ [43/128, 29/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 183500800 184811520 281804800 287375360 ⟨⟨125034213016, 125034213025⟩, ⟨120450596511, 129687302302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 184811520 186122240 281804800 287375360 ⟨⟨124056289581, 124056289587⟩, ⟨119499326562, 128682160048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 183500800 184811520 287375360 292945920 ⟨⟨127278289467, 127278289475⟩, ⟨122677795277, 131948154696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 184811520 186122240 287375360 292945920 ⟨⟨126285667235, 126285667242⟩, ⟨121711858674, 130928287961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 186122240 187432960 281804800 287375360 ⟨⟨123084642343, 123084642347⟩, ⟨118554064882, 127683569055⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 187432960 188743680 281804800 287375360 ⟨⟨122119178681, 122119178689⟩, ⟨117614723082, 126691432352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 186122240 187432960 287375360 292945920 ⟨⟨125299356223, 125299356227⟩, ⟨120751966905, 129915005800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 187432960 188743680 287375360 292945920 ⟨⟨124319263786, 124319263794⟩, ⟨119798031502, 128908211277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 183500800 184811520 292945920 298516480 ⟨⟨129516207930, 129516207939⟩, ⟨124898917654, 134202765792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 184811520 186122240 292945920 298516480 ⟨⟨128509010289, 128509010296⟩, ⟨123918435578, 133168300177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 183500800 184811520 298516480 304087040 ⟨⟨131748045565, 131748045573⟩, ⟨127114039551, 136451214006⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 184811520 186122240 298516480 304087040 ⟨⟨130726393871, 130726393879⟩, ⟨126119131201, 135402273035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 186122240 187432960 292945920 298516480 ⟨⟨127508156844, 127508156846⟩, ⟨122944032888, 132140450367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 187432960 188743680 292945920 298516480 ⟨⟨126513554953, 126513554960⟩, ⟨121975621071, 131119119488⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 186122240 187432960 298516480 304087040 ⟨⟨129711117350, 129711117354⟩, ⟨125130334825, 134359977069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 187432960 188743680 298516480 304087040 ⟨⟨128702123397, 128702123406⟩, ⟨124147561893, 133324229327⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 183500800 188743680 281804800 304087040 t = true :=
  ⟨_, (join_sr (m := 292945920) (by decide) (join_su (m := 186122240) (by decide) (join_sr (m := 287375360) (by decide) (join_su (m := 184811520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 184811520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 287375360) (by decide) (join_su (m := 187432960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 187432960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 186122240) (by decide) (join_sr (m := 298516480) (by decide) (join_su (m := 184811520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 184811520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 298516480) (by decide) (join_su (m := 187432960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 187432960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/32 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (43/128 : ℝ) (29/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  have e3 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

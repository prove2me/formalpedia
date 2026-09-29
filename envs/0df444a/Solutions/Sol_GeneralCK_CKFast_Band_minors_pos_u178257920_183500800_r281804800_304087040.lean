-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_183500800_r281804800_304087040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:46:48.2129+00:00
-- url     : https://prove2.me/submissions/3f885bfd-c3cb-43a5-8ff4-32c14724540e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 7/32]`, `ρ ∈ [43/128, 29/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 179568640 281804800 287375360 ⟨⟨129010582151, 129010582157⟩, ⟨124317584774, 133775387505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 179568640 180879360 281804800 287375360 ⟨⟨128006592732, 128006592736⟩, ⟨123341364607, 132743033690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 178257920 179568640 287375360 292945920 ⟨⟨131313804080, 131313804089⟩, ⟨126603816994, 136095469797⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 179568640 180879360 287375360 292945920 ⟨⟨130294975771, 130294975774⟩, ⟨125612783343, 135048258860⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 180879360 182190080 281804800 287375360 ⟨⟨127009267593, 127009267601⟩, ⟨122371522989, 131717637544⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 182190080 183500800 281804800 287375360 ⟨⟨126018506988, 126018506997⟩, ⟨121407964757, 130699094592⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 180879360 182190080 287375360 292945920 ⟨⟨129282846741, 129282846748⟩, ⟨124628165013, 134008038634⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 182190080 183500800 287375360 292945920 ⟨⟨128277317270, 128277317278⟩, ⟨123649866808, 132974704732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 178257920 179568640 292945920 298516480 ⟨⟨133610353383, 133610353390⟩, ⟨128883467366, 138408786946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 179568640 180879360 292945920 298516480 ⟨⟨132576818069, 132576818071⟩, ⟨127877749767, 137346853128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 178257920 179568640 298516480 304087040 ⟨⟨135900315865, 135900315873⟩, ⟨131156620254, 140715426220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 179568640 180879360 298516480 304087040 ⟨⟨134852203187, 134852203191⟩, ⟨130136346051, 139638901464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 180879360 182190080 292945920 298516480 ⟨⟨131550014862, 131550014869⟩, ⟨126878482127, 136291940854⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 182190080 183500800 292945920 298516480 ⟨⟨130529844099, 130529844108⟩, ⟨125885569245, 135243945859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 180879360 182190080 298516480 304087040 ⟨⟨133810853330, 133810853339⟩, ⟨129122554364, 138569426935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 182190080 183500800 298516480 304087040 ⟨⟨132776166716, 132776166725⟩, ⟨128115150016, 137506898521⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 183500800 281804800 304087040 t = true :=
  ⟨_, (join_sr (m := 292945920) (by decide) (join_su (m := 180879360) (by decide) (join_sr (m := 287375360) (by decide) (join_su (m := 179568640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 179568640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 287375360) (by decide) (join_su (m := 182190080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 182190080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 180879360) (by decide) (join_sr (m := 298516480) (by decide) (join_su (m := 179568640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 179568640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 298516480) (by decide) (join_su (m := 182190080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 182190080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (43/128 : ℝ) (29/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  have e3 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

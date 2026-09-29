-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_251658240_r393216000_404357120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:12:04.926759+00:00
-- url     : https://prove2.me/submissions/40f370a3-ed12-4750-8384-b24031b41e84

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 3/10]`, `ρ ∈ [15/32, 617/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247726080 393216000 396001280 ⟨⟨114603106307, 114603106313⟩, ⟨111271100677, 117971681466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246415360 247726080 396001280 398786560 ⟨⟨115372478597, 115372478604⟩, ⟨112033846102, 118747715747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247726080 249036800 393216000 396001280 ⟨⟨113593906723, 113593906731⟩, ⟨110275311138, 116948906167⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247726080 249036800 396001280 398786560 ⟨⟨114357161065, 114357161072⟩, ⟨111031960614, 117718801216⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 246415360 247726080 398786560 401571840 ⟨⟨116141416672, 116141416678⟩, ⟨112796158270, 119523314689⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246415360 247726080 401571840 404357120 ⟨⟨116909922751, 116909922759⟩, ⟨113558039389, 120298480522⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247726080 249036800 398786560 401571840 ⟨⟨115119991688, 115119991695⟩, ⟨111788187188, 118488271573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247726080 249036800 401571840 404357120 ⟨⟨115882400751, 115882400759⟩, ⟨112543993006, 119257319401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 250347520 393216000 396001280 ⟨⟨112588275870, 112588275877⟩, ⟨109282994464, 115929796858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249036800 250347520 396001280 398786560 ⟨⟨113345417498, 113345417504⟩, ⟨110033553463, 116693557659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 250347520 251658240 393216000 396001280 ⟨⟨111586168463, 111586168468⟩, ⟨108294106477, 114914307136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 250347520 251658240 396001280 398786560 ⟨⟨112337202615, 112337202621⟩, ⟨109038580471, 115671938680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249036800 250347520 398786560 401571840 ⟨⟨114102145718, 114102145726⟩, ⟨110783699733, 117456904222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 249036800 250347520 401571840 404357120 ⟨⟨114858462631, 114858462637⟩, ⟨111533435356, 118219838653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 250347520 251658240 398786560 401571840 ⟨⟨113087833491, 113087833496⟩, ⟨109782651725, 116429166257⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250347520 251658240 401571840 404357120 ⟨⟨113838063125, 113838063133⟩, ⟨110526322267, 117185991911⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 251658240 393216000 404357120 t = true :=
  ⟨_, (join_su (m := 249036800) (by decide) (join_sr (m := 398786560) (by decide) (join_su (m := 247726080) (by decide) (join_sr (m := 396001280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 396001280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 247726080) (by decide) (join_sr (m := 401571840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 401571840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 398786560) (by decide) (join_su (m := 250347520) (by decide) (join_sr (m := 396001280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 396001280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 250347520) (by decide) (join_sr (m := 401571840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 401571840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (15/32 : ℝ) (617/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  have e3 : (((404357120 : ℤ) : ℝ) / (D : ℝ)) = (617/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

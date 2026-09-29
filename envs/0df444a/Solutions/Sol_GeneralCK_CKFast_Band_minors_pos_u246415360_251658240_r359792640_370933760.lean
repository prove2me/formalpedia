-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_251658240_r359792640_370933760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:01:15.863078+00:00
-- url     : https://prove2.me/submissions/2d97baee-cbab-4899-8591-be6b16ef589a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 3/10]`, `ρ ∈ [549/1280, 283/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247726080 359792640 362577920 ⟨⟨105335952998, 105335953005⟩, ⟨102083548448, 108624492836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246415360 247726080 362577920 365363200 ⟨⟨106110711434, 106110711442⟩, ⟨102851667676, 109405927558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247726080 249036800 359792640 362577920 ⟨⟨104401010744, 104401010751⟩, ⟨101161740822, 107676241973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247726080 249036800 362577920 365363200 ⟨⟨105169520283, 105169520291⟩, ⟨101923634922, 108451404696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 246415360 247726080 365363200 368148480 ⟨⟨106885008495, 106885008503⟩, ⟨103619326617, 110186899656⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246415360 247726080 368148480 370933760 ⟨⟨107658846484, 107658846490⟩, ⟨104386527560, 110967411444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247726080 249036800 365363200 368148480 ⟨⟨105937579718, 105937579725⟩, ⟨102685079855, 109226116223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247726080 249036800 368148480 370933760 ⟨⟨106705191282, 106705191289⟩, ⟨103446077843, 110000378797⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 250347520 359792640 362577920 ⟨⟨103469559370, 103469559376⟩, ⟨100243325624, 106731582033⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249036800 250347520 362577920 365363200 ⟨⟨104231827593, 104231827600⟩, ⟨100999002376, 107500480128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 250347520 251658240 359792640 362577920 ⟨⟨102541553719, 102541553726⟩, ⟨99328258872, 105790466672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 250347520 251658240 362577920 365363200 ⟨⟨103297588183, 103297588191⟩, ⟨100077726024, 106553107488⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249036800 250347520 365363200 368148480 ⟨⟨104993656777, 104993656784⟩, ⟨101754240877, 108268938244⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 249036800 250347520 368148480 370933760 ⟨⟨105755049093, 105755049100⟩, ⟨102509043289, 109036958557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 250347520 251658240 365363200 368148480 ⟨⟨104053194473, 104053194480⟩, ⟨100826765645, 107315319335⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250347520 251658240 368148480 370933760 ⟨⟨104808374695, 104808374702⟩, ⟨101575379835, 108077104330⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 251658240 359792640 370933760 t = true :=
  ⟨_, (join_su (m := 249036800) (by decide) (join_sr (m := 365363200) (by decide) (join_su (m := 247726080) (by decide) (join_sr (m := 362577920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 362577920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 247726080) (by decide) (join_sr (m := 368148480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 368148480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 365363200) (by decide) (join_su (m := 250347520) (by decide) (join_sr (m := 362577920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 362577920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 250347520) (by decide) (join_sr (m := 368148480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 368148480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (549/1280 : ℝ) (283/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((359792640 : ℤ) : ℝ) / (D : ℝ)) = (549/1280 : ℝ) := by norm_num [D]
  have e3 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

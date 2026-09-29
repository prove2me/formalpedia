-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_209715200_r292945920_304087040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:39:52.193989+00:00
-- url     : https://prove2.me/submissions/6139bbad-e001-447e-b117-27b5c4fbb688

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 1/4]`, `ρ ∈ [447/1280, 29/80]` by 14 cells of the computing
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
theorem cell0 : cellOK 204472320 205783040 292945920 295731200 ⟨⟨113611566963, 113611566971⟩, ⟨110055377484, 117210229670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 204472320 205783040 295731200 298516480 ⟨⟨114614799787, 114614799795⟩, ⟨111051150440, 118220934254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 205783040 207093760 292945920 295731200 ⟨⟨112699123605, 112699123610⟩, ⟨109159554268, 116280896460⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205783040 207093760 295731200 298516480 ⟨⟨113695353579, 113695353584⟩, ⟨110148345151, 117284578724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 204472320 205783040 298516480 304087040 ⟨⟨116117611482, 116117611489⟩, ⟨111882050431, 120414339131⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 205783040 207093760 298516480 304087040 ⟨⟨115187704214, 115187704219⟩, ⟨110975120590, 119461002760⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 207093760 208404480 292945920 295731200 ⟨⟨111791712711, 111791712718⟩, ⟨108268605621, 115356756778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 207093760 208404480 295731200 298516480 ⟨⟨112780955448, 112780955455⟩, ⟨109250430397, 116353431953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 208404480 209715200 292945920 295731200 ⟨⟨110889263979, 110889263986⟩, ⟨107382463514, 114437737989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 208404480 209715200 295731200 298516480 ⟨⟨111871535038, 111871535045⟩, ⟨108357338082, 115427421261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 207093760 208404480 298516480 301301760 ⟨⟨113769156222, 113769156230⟩, ⟨110231221769, 117349056312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 207093760 208404480 301301760 304087040 ⟨⟨114756320900, 114756320906⟩, ⟨111210985553, 118343635772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 208404480 209715200 298516480 301301760 ⟨⟨112852786430, 112852786437⟩, ⟨109331201223, 116416076336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 208404480 209715200 301301760 304087040 ⟨⟨113833023862, 113833023869⟩, ⟨110304058595, 117403708971⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 209715200 292945920 304087040 t = true :=
  ⟨_, (join_su (m := 207093760) (by decide) (join_sr (m := 298516480) (by decide) (join_su (m := 205783040) (by decide) (join_sr (m := 295731200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 295731200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 205783040) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 298516480) (by decide) (join_su (m := 208404480) (by decide) (join_sr (m := 295731200) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 295731200) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 208404480) (by decide) (join_sr (m := 301301760) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 301301760) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (447/1280 : ℝ) (29/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  have e3 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

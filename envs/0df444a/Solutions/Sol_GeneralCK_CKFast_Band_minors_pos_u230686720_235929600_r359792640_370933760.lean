-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_235929600_r359792640_370933760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:50:29.688663+00:00
-- url     : https://prove2.me/submissions/d2658296-0035-4ab6-a8a3-208dcf25a441

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 9/32]`, `ρ ∈ [549/1280, 283/640]` by 14 cells of the computing
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
theorem cell0 : cellOK 230686720 231997440 359792640 362577920 ⟨⟨116844792446, 116844792452⟩, ⟨113426640381, 120301299324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 231997440 362577920 365363200 ⟨⟨117695135804, 117695135810⟩, ⟨114270076870, 121158577194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231997440 233308160 359792640 362577920 ⟨⟨115864219880, 115864219884⟩, ⟨112460482319, 119306117537⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231997440 233308160 362577920 365363200 ⟨⟨116708222031, 116708222034⟩, ⟨113297598523, 120157034172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 231997440 365363200 370933760 ⟨⟨118969501473, 118969501480⟩, ⟨114978921315, 123013601558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 231997440 233308160 365363200 370933760 ⟨⟨117973101993, 117973101997⟩, ⟨114002521212, 121996872035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233308160 234618880 359792640 362577920 ⟨⟨114887727553, 114887727561⟩, ⟨111498290453, 118315131885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 233308160 234618880 362577920 365363200 ⟨⟨115725396244, 115725396250⟩, ⟨112329094392, 119159694736⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 234618880 235929600 359792640 362577920 ⟨⟨113915262737, 113915262743⟩, ⟨110540013457, 117328288203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 234618880 235929600 362577920 365363200 ⟨⟨114746605709, 114746605717⟩, ⟨111364513144, 118166504724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 233308160 234618880 365363200 368148480 ⟨⟨116562479033, 116562479040⟩, ⟨113159315223, 120003668691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 233308160 234618880 368148480 370933760 ⟨⟨117398978979, 117398978987⟩, ⟨113988955985, 120847056827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 234618880 235929600 365363200 368148480 ⟨⟨115577376244, 115577376252⟩, ⟨112188442999, 119004146003⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 234618880 235929600 368148480 370933760 ⟨⟨116407577316, 116407577322⟩, ⟨113011805974, 119841215033⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 235929600 359792640 370933760 t = true :=
  ⟨_, (join_su (m := 233308160) (by decide) (join_sr (m := 365363200) (by decide) (join_su (m := 231997440) (by decide) (join_sr (m := 362577920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 362577920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 231997440) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 365363200) (by decide) (join_su (m := 234618880) (by decide) (join_sr (m := 362577920) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 362577920) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 234618880) (by decide) (join_sr (m := 368148480) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 368148480) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (549/1280 : ℝ) (283/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((359792640 : ℤ) : ℝ) / (D : ℝ)) = (549/1280 : ℝ) := by norm_num [D]
  have e3 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

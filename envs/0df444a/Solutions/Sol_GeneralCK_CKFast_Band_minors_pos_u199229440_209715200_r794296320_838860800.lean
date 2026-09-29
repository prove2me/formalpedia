-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_209715200_r794296320_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:12:21.105475+00:00
-- url     : https://prove2.me/submissions/6bf05e1e-c5de-4a49-98aa-bbe4b6b77da2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 1/4]`, `ρ ∈ [303/320, 1]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 201850880 794296320 805437440 ⟨⟨289680763198, 289680763208⟩, ⟨278492468072, 301083863629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 201850880 204472320 794296320 805437440 ⟨⟨285795824032, 285795824037⟩, ⟨274700236913, 297106138228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 199229440 201850880 805437440 816578560 ⟨⟨293284323416, 293284323426⟩, ⟨282041659391, 304740426707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 201850880 204472320 805437440 816578560 ⟨⟨289362012376, 289362012379⟩, ⟨278211797807, 300725675733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 204472320 207093760 794296320 805437440 ⟨⟨281927893695, 281927893705⟩, ⟨270924440906, 293145952315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 207093760 209715200 794296320 805437440 ⟨⟨278076624825, 278076624835⟩, ⟨267164738599, 289202953949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 204472320 207093760 805437440 816578560 ⟨⟨285456452296, 285456452307⟩, ⟨274398141106, 296728176803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 207093760 209715200 805437440 816578560 ⟨⟨281567302335, 281567302344⟩, ⟨270600353727, 292747585142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 199229440 201850880 816578560 827719680 ⟨⟨296882942500, 296882942510⟩, ⟨285585991596, 308391939608⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 201850880 204472320 816578560 827719680 ⟨⟨292923418815, 292923418820⟩, ⟨281718653216, 304340328190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 199229440 201850880 827719680 838860800 ⟨⟨300476833742, 300476833753⟩, ⟨289125672746, 312038620542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 201850880 204472320 827719680 838860800 ⟨⟨296480248866, 296480248871⟩, ⟨285221003637, 307950305824⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 204472320 207093760 816578560 827719680 ⟨⟨288980385592, 288980385602⟩, ⟨277867286756, 300305678832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 207093760 209715200 816578560 827719680 ⟨⟨285053508457, 285053508468⟩, ⟨274031562521, 296287653853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 204472320 207093760 827719680 838860800 ⟨⟨292499891509, 292499891519⟩, ⟨281332070985, 303878660829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 207093760 209715200 827719680 838860800 ⟨⟨288535433721, 288535433731⟩, ⟨277458550924, 299823354911⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 209715200 794296320 838860800 t = true :=
  ⟨_, (join_sr (m := 816578560) (by decide) (join_su (m := 204472320) (by decide) (join_sr (m := 805437440) (by decide) (join_su (m := 201850880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 201850880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 805437440) (by decide) (join_su (m := 207093760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 207093760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 204472320) (by decide) (join_sr (m := 827719680) (by decide) (join_su (m := 201850880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 201850880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 827719680) (by decide) (join_su (m := 207093760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 207093760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (303/320 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((794296320 : ℤ) : ℝ) / (D : ℝ)) = (303/320 : ℝ) := by norm_num [D]
  have e3 : (((838860800 : ℤ) : ℝ) / (D : ℝ)) = (1 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

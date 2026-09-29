-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_251658240_r437780480_460062720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:21:56.122108+00:00
-- url     : https://prove2.me/submissions/fa34aea9-0334-4570-95cd-3859648989d7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 3/10]`, `ρ ∈ [167/320, 351/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247726080 437780480 443351040 ⟨⟨127243582370, 127243582377⟩, ⟨123300636980, 131237031538⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 247726080 249036800 437780480 443351040 ⟨⟨126134740963, 126134740970⟩, ⟨122210775394, 130108941434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246415360 247726080 443351040 448921600 ⟨⟨128768159257, 128768159265⟩, ⟨124811202160, 132775672890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247726080 249036800 443351040 448921600 ⟨⟨127647422231, 127647422238⟩, ⟨123709491391, 131635643031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249036800 250347520 437780480 443351040 ⟨⟨125029531807, 125029531814⟩, ⟨121124423831, 128984607700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 250347520 251658240 437780480 443351040 ⟨⟨123927909967, 123927909974⟩, ⟨120041538678, 127863984064⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249036800 250347520 443351040 448921600 ⟨⟨126530321999, 126530322006⟩, ⟨122611295865, 130499373358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 250347520 251658240 443351040 448921600 ⟨⟨125416813705, 125416813713⟩, ⟨121516572024, 129366817699⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 246415360 247726080 448921600 454492160 ⟨⟨130291151015, 130291151022⟩, ⟨126320189218, 134312721248⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 247726080 249036800 448921600 454492160 ⟨⟨129158556141, 129158556147⟩, ⟨125206666404, 133160790060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 246415360 247726080 454492160 460062720 ⟨⟨131812574509, 131812574517⟩, ⟨127827614889, 135848193610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 247726080 249036800 454492160 460062720 ⟨⟨130668159097, 130668159104⟩, ⟨126702316708, 134684399053⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249036800 250347520 448921600 454492160 ⟨⟨128029601959, 128029601967⟩, ⟨124096663413, 132012622220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250347520 251658240 448921600 454492160 ⟨⟨126904243700, 126904243707⟩, ⟨122990136762, 130868171654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 249036800 250347520 454492160 460062720 ⟨⟨129527387641, 129527387649⟩, ⟨125580542312, 133524370355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250347520 251658240 454492160 460062720 ⟨⟨128390215462, 128390215470⟩, ⟨124462248290, 132368061553⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 251658240 437780480 460062720 t = true :=
  ⟨_, (join_sr (m := 448921600) (by decide) (join_su (m := 249036800) (by decide) (join_sr (m := 443351040) (by decide) (join_su (m := 247726080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 247726080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 443351040) (by decide) (join_su (m := 250347520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 250347520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 249036800) (by decide) (join_sr (m := 454492160) (by decide) (join_su (m := 247726080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 247726080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 454492160) (by decide) (join_su (m := 250347520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 250347520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (167/320 : ℝ) (351/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  have e3 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

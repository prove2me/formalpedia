-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_199229440_r348651520_370933760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:42:50.270987+00:00
-- url     : https://prove2.me/submissions/1a1a827e-7c6f-47bc-9031-dc66e1739953

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 19/80]`, `ρ ∈ [133/320, 283/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 193986560 195297280 348651520 354222080 ⟨⟨142579472834, 142579472841⟩, ⟨138006940359, 147216388993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 195297280 196608000 348651520 354222080 ⟨⟨141482982774, 141482982781⟩, ⟨136935471158, 146094430258⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 193986560 195297280 354222080 359792640 ⟨⟨144648180762, 144648180769⟩, ⟨140059789468, 149300882290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 195297280 196608000 354222080 359792640 ⟨⟨143538460776, 143538460783⟩, ⟨138975112486, 148165676871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 196608000 197918720 348651520 354222080 ⟨⟨140392376135, 140392376142⟩, ⟨135869664837, 144978580127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 197918720 199229440 348651520 354222080 ⟨⟨139307573067, 139307573074⟩, ⟨134809444625, 143868755611⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 196608000 197918720 354222080 359792640 ⟨⟨142434639483, 142434639491⟩, ⟨137896115154, 147036593707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 197918720 199229440 354222080 359792640 ⟨⟨141336637200, 141336637208⟩, ⟨136822720821, 145913550017⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 195297280 359792640 365363200 ⟨⟨146712365911, 146712365917⟩, ⟨142108170513, 151380796558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 195297280 196608000 359792640 365363200 ⟨⟨145589505535, 145589505542⟩, ⟨141010373745, 150232435547⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 193986560 195297280 365363200 370933760 ⟨⟨148772082939, 148772082948⟩, ⟨144152137382, 153456187243⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 195297280 196608000 365363200 370933760 ⟨⟨147636170338, 147636170345⟩, ⟨143041307469, 152294760334⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 196608000 197918720 359792640 365363200 ⟨⟨144472557743, 144472557751⟩, ⟨139918272032, 149090209040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 197918720 199229440 359792640 365363200 ⟨⟨143361443036, 143361443044⟩, ⟨138831788869, 147954034484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 196608000 197918720 365363200 370933760 ⟨⟨146506182859, 146506182868⟩, ⟨141936186692, 151139478802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 197918720 199229440 365363200 370933760 ⟨⟨145382041206, 145382041215⟩, ⟨140836698699, 149990260345⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 199229440 348651520 370933760 t = true :=
  ⟨_, (join_sr (m := 359792640) (by decide) (join_su (m := 196608000) (by decide) (join_sr (m := 354222080) (by decide) (join_su (m := 195297280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 195297280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 354222080) (by decide) (join_su (m := 197918720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 197918720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 196608000) (by decide) (join_sr (m := 365363200) (by decide) (join_su (m := 195297280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 195297280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 365363200) (by decide) (join_su (m := 197918720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 197918720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (133/320 : ℝ) (283/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  have e3 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_183500800_r259522560_281804800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:46:48.22701+00:00
-- url     : https://prove2.me/submissions/6ee6b96f-2909-44f4-b567-e379fdeb5042

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 7/32]`, `ρ ∈ [99/320, 43/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 179568640 259522560 265093120 ⟨⟨119729212240, 119729212246⟩, ⟨115105111250, 124425620918⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 179568640 180879360 259522560 265093120 ⟨⟨118785943642, 118785943646⟩, ⟨114189485687, 123454085472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 178257920 179568640 265093120 270663680 ⟨⟨122060005544, 122060005550⟩, ⟨117418536785, 126773659750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 179568640 180879360 265093120 270663680 ⟨⟨121101347205, 121101347208⟩, ⟨116487556835, 125786706368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 180879360 182190080 259522560 265093120 ⟨⟨117849176429, 117849176437⟩, ⟨113280069087, 122489352253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 182190080 183500800 259522560 265093120 ⟨⟨116918811111, 116918811119⟩, ⟨112376766782, 121531316783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 180879360 182190080 265093120 270663680 ⟨⟨120149234528, 120149234535⟩, ⟨115562831734, 124806597690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 182190080 183500800 265093120 270663680 ⟨⟨119203567906, 119203567913⟩, ⟨114644266637, 123833229182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 178257920 179568640 270663680 276234240 ⟨⟨124383771540, 124383771548⟩, ⟨119725031821, 129114572662⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 179568640 180879360 270663680 276234240 ⟨⟨123409864756, 123409864759⟩, ⟨118778836210, 128112345218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 178257920 179568640 276234240 281804800 ⟨⟨126700600661, 126700600669⟩, ⟨122024685243, 131448451655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 179568640 180879360 276234240 281804800 ⟨⟨125711584309, 125711584313⟩, ⟨121063410332, 130431091543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 180879360 182190080 270663680 276234240 ⟨⟨122442545502, 122442545509⟩, ⟨117838938965, 127117002500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 182190080 183500800 270663680 276234240 ⟨⟨121481714088, 121481714094⟩, ⟨116905245105, 126128439959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 180879360 182190080 276234240 281804800 ⟨⟨124729195004, 124729195012⟩, ⟨120108475001, 129420653791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 182190080 183500800 276234240 281804800 ⟨⟨123753333015, 123753333022⟩, ⟨119159784164, 128417033871⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 183500800 259522560 281804800 t = true :=
  ⟨_, (join_sr (m := 270663680) (by decide) (join_su (m := 180879360) (by decide) (join_sr (m := 265093120) (by decide) (join_su (m := 179568640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 179568640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 265093120) (by decide) (join_su (m := 182190080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 182190080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 180879360) (by decide) (join_sr (m := 276234240) (by decide) (join_su (m := 179568640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 179568640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 276234240) (by decide) (join_su (m := 182190080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 182190080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (99/320 : ℝ) (43/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  have e3 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

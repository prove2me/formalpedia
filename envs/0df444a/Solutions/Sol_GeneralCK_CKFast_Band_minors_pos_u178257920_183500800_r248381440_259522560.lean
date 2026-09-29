-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_183500800_r248381440_259522560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:19:07.955997+00:00
-- url     : https://prove2.me/submissions/490ff10b-51c3-4c8a-bedc-7f51629d82a9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 7/32]`, `ρ ∈ [379/1280, 99/320]` by 14 cells of the computing
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
theorem cell0 : cellOK 178257920 179568640 248381440 251166720 ⟨⟨114458757020, 114458757027⟩, ⟨110659971535, 118306468287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178257920 179568640 251166720 253952000 ⟨⟨115633138154, 115633138162⟩, ⟨111826279995, 119488905787⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 179568640 180879360 248381440 251166720 ⟨⟨113550644795, 113550644799⟩, ⟨109771958337, 117377877691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 179568640 180879360 251166720 253952000 ⟨⟨114717149037, 114717149040⟩, ⟨110930408563, 118552421758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 178257920 179568640 253952000 259522560 ⟨⟨117391299984, 117391299992⟩, ⟨112784665143, 122070362934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 179568640 180879360 253952000 259522560 ⟨⟨116463564889, 116463564892⟩, ⟨111884535099, 121114391818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 180879360 182190080 248381440 251166720 ⟨⟨112648925185, 112648925193⟩, ⟨108890113262, 116455909496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 180879360 182190080 251166720 253952000 ⟨⟨113807577826, 113807577832⟩, ⟨110040731102, 117622584810⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 182190080 183500800 248381440 251166720 ⟨⟨111753499115, 111753499123⟩, ⟨108014341000, 115540460752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 182190080 183500800 251166720 253952000 ⟨⟨112904325334, 112904325342⟩, ⟨109157152165, 116699291906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 180879360 182190080 253952000 256737280 ⟨⟨114964483349, 114964483356⟩, ⟨111189620123, 118787494311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 180879360 182190080 256737280 259522560 ⟨⟨116119652893, 116119652901⟩, ⟨112336791328, 119950649271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 182190080 183500800 253952000 256737280 ⟨⟨114053440200, 114053440208⟩, ⟨110298269749, 117856393540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 182190080 183500800 256737280 259522560 ⟨⟨115200854546, 115200854554⟩, ⟨111437704451, 119011776620⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 183500800 248381440 259522560 t = true :=
  ⟨_, (join_su (m := 180879360) (by decide) (join_sr (m := 253952000) (by decide) (join_su (m := 179568640) (by decide) (join_sr (m := 251166720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 251166720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 179568640) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 253952000) (by decide) (join_su (m := 182190080) (by decide) (join_sr (m := 251166720) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 251166720) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 182190080) (by decide) (join_sr (m := 256737280) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 256737280) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (379/1280 : ℝ) (99/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  have e3 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

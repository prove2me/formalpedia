-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_249036800_r192675840_198246400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:21:23.37792+00:00
-- url     : https://prove2.me/submissions/4aaa4f52-d177-4489-9400-cc4ca79f02d2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 19/64]`, `ρ ∈ [147/640, 121/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247070720 192675840 194068480 ⟨⟨57846881908, 57846881914⟩, ⟨56416265264, 59285916479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246415360 247070720 194068480 195461120 ⟨⟨58251393616, 58251393621⟩, ⟨56819090806, 59692120101⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247070720 247726080 192675840 194068480 ⟨⟨57578765791, 57578765795⟩, ⟨56151024446, 59014899101⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247070720 247726080 194068480 195461120 ⟨⟨57981507896, 57981507897⟩, ⟨56552084653, 59419328877⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 246415360 247070720 195461120 196853760 ⟨⟨58655750264, 58655750269⟩, ⟨57221761515, 60098168430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246415360 247070720 196853760 198246400 ⟨⟨59059952209, 59059952215⟩, ⟨57624277744, 60504061823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247070720 247726080 195461120 196853760 ⟨⟨58384096952, 58384096956⟩, ⟨56952992026, 59823605386⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247070720 247726080 196853760 198246400 ⟨⟨58786533314, 58786533318⟩, ⟨57353746915, 60227728978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 247726080 248381440 192675840 194068480 ⟨⟨57311303820, 57311303827⟩, ⟨55886424701, 58744549105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 247726080 248381440 194068480 195461120 ⟨⟨57712279273, 57712279278⟩, ⟨56285722521, 59147207991⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 248381440 249036800 192675840 194068480 ⟨⟨57044491281, 57044491286⟩, ⟨55622461401, 58474861680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 248381440 249036800 194068480 195461120 ⟨⟨57443703018, 57443703023⟩, ⟨56019999767, 58875752616⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 247726080 248381440 195461120 196853760 ⟨⟨58113103672, 58113103678⟩, ⟨56684869488, 59549715616⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 247726080 248381440 196853760 198246400 ⟨⟨58513777362, 58513777368⟩, ⟨57083865945, 59952072322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 248381440 249036800 195461120 196853760 ⟨⟨57842765674, 57842765680⟩, ⟨56417389238, 59276494274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 248381440 249036800 196853760 198246400 ⟨⟨58241679587, 58241679594⟩, ⟨56814630156, 59677086993⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 249036800 192675840 198246400 t = true :=
  ⟨_, (join_su (m := 247726080) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 247070720) (by decide) (join_sr (m := 194068480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 194068480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 247070720) (by decide) (join_sr (m := 196853760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 196853760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 195461120) (by decide) (join_su (m := 248381440) (by decide) (join_sr (m := 194068480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 194068480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 248381440) (by decide) (join_sr (m := 196853760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 196853760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (121/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((198246400 : ℤ) : ℝ) / (D : ℝ)) = (121/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

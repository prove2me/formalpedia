-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_220200960_r772014080_794296320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:08:45.527353+00:00
-- url     : https://prove2.me/submissions/b12f66ef-d020-4b19-ae75-d04b61d40b31

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 21/80]`, `ρ ∈ [589/640, 303/320]` by 11 cells of the computing
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
theorem cell0 : cellOK 209715200 212336640 772014080 783155200 ⟨⟨267322872690, 267322872699⟩, ⟨256612666746, 278249296021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 212336640 214958080 772014080 783155200 ⟨⟨263581117459, 263581117469⟩, ⟨252961645534, 274416405718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 209715200 212336640 783155200 794296320 ⟨⟨270784620867, 270784620877⟩, ⟨260019042988, 281765439802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212336640 214958080 783155200 794296320 ⟨⟨267004182360, 267004182370⟩, ⟨256329198729, 277894085129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 214958080 217579520 772014080 777584640 ⟨⟨259008739188, 259008739193⟩, ⟨249838387033, 268339359527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 214958080 217579520 777584640 783155200 ⟨⟨260701938800, 260701938805⟩, ⟨251505076494, 270058856871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 217579520 220200960 772014080 777584640 ⟨⟨255308697868, 255308697878⟩, ⟨246203851515, 264573771732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 217579520 220200960 777584640 783155200 ⟨⟨256982291875, 256982291885⟩, ⟨247850896164, 266273729454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 217579520 783155200 794296320 ⟨⟨263239635951, 263239635956⟩, ⟨252654670716, 274039162473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 217579520 220200960 783155200 788725760 ⟨⟨258654801457, 258654801466⟩, ⟨249496864594, 267972589484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 220200960 788725760 794296320 ⟨⟨260326247473, 260326247482⟩, ⟨251141777280, 269670373032⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 220200960 772014080 794296320 t = true :=
  ⟨_, (join_su (m := 214958080) (by decide) (join_sr (m := 783155200) (by decide) (join_su (m := 212336640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 212336640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 783155200) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 777584640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 777584640) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 217579520) (by decide) (leaf_ok cell8) (join_sr (m := 788725760) (by decide) (leaf_ok cell9) (leaf_ok cell10)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (589/640 : ℝ) (303/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((772014080 : ℤ) : ℝ) / (D : ℝ)) = (589/640 : ℝ) := by norm_num [D]
  have e3 : (((794296320 : ℤ) : ℝ) / (D : ℝ)) = (303/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

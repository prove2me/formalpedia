-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_243793920_r192675840_198246400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:10:51.702521+00:00
-- url     : https://prove2.me/submissions/ced0d8c6-9f38-483c-aed5-d5ee05cd6652

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 93/320]`, `ρ ∈ [147/640, 121/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 241827840 192675840 194068480 ⟨⟨60015938577, 60015938582⟩, ⟨58561837761, 61478670848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241172480 241827840 194068480 195461120 ⟨⟨60434715469, 60434715474⟩, ⟨58978894211, 61899173710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241827840 242483200 192675840 194068480 ⟨⟨59742414973, 59742414978⟩, ⟨58291297398, 61202136733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 241827840 242483200 194068480 195461120 ⟨⟨60159398023, 60159398028⟩, ⟨58706564302, 61620841484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241172480 241827840 195461120 196853760 ⟨⟨60853320428, 60853320434⟩, ⟨59395779060, 62319504297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 241172480 241827840 196853760 198246400 ⟨⟨61271753857, 61271753863⟩, ⟨59812492708, 62739663014⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 241827840 242483200 195461120 196853760 ⟨⟨60576211325, 60576211330⟩, ⟨59121661776, 62039376161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 241827840 242483200 196853760 198246400 ⟨⟨60992855277, 60992855282⟩, ⟨59536590216, 62457741160⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 242483200 243138560 192675840 194068480 ⟨⟨59469584601, 59469584608⟩, ⟨58021436440, 60926309843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 242483200 243138560 194068480 195461120 ⟨⟨59884776899, 59884776905⟩, ⟨58434916885, 61343219577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243138560 243793920 192675840 194068480 ⟨⟨59197442443, 59197442450⟩, ⟨57752249968, 60651185063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 243138560 243793920 194068480 195461120 ⟨⟨59610847062, 59610847067⟩, ⟨58163947024, 61066302855⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 242483200 243138560 195461120 196853760 ⟨⟨60299801611, 60299801618⟩, ⟨58848230050, 61759961413⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 242483200 243138560 196853760 198246400 ⟨⟨60714659132, 60714659137⟩, ⟨59261376325, 62176535745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 243138560 243793920 195461120 196853760 ⟨⟨60024086236, 60024086241⟩, ⟨58575478927, 61481254906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 243138560 243793920 196853760 198246400 ⟨⟨60437160353, 60437160358⟩, ⟨58986846062, 61896041601⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 243793920 192675840 198246400 t = true :=
  ⟨_, (join_su (m := 242483200) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 241827840) (by decide) (join_sr (m := 194068480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 194068480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 241827840) (by decide) (join_sr (m := 196853760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 196853760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 195461120) (by decide) (join_su (m := 243138560) (by decide) (join_sr (m := 194068480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 194068480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 243138560) (by decide) (join_sr (m := 196853760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 196853760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (121/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((198246400 : ℤ) : ℝ) / (D : ℝ)) = (121/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

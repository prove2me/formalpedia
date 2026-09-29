-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_167772160_r237240320_249036800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:56:44.51732+00:00
-- url     : https://prove2.me/submissions/89e0c258-d5b3-49d6-b2b3-e6e37688a170

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 1/5]`, `ρ ∈ [181/640, 19/64]` by 11 cells of the computing
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
theorem cell0 : cellOK 162529280 163840000 237240320 243138560 ⟨⟨121502257651, 121502257660⟩, ⟨116489868894, 126599539003⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 163840000 165150720 237240320 240189440 ⟨⟨119863806988, 119863806995⟩, ⟨115809669952, 123973060167⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 163840000 165150720 240189440 243138560 ⟨⟨121210463823, 121210463832⟩, ⟨117147448694, 125328547109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 162529280 163840000 243138560 249036800 ⟨⟨124207956942, 124207956951⟩, ⟨119176122858, 129324434018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 163840000 165150720 243138560 249036800 ⟨⟨123225541612, 123225541619⟩, ⟨118226217770, 128308699872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 165150720 166461440 237240320 240189440 ⟨⟨118911091159, 118911091166⟩, ⟨114880238902, 122996586951⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 165150720 166461440 240189440 243138560 ⟨⟨120248915031, 120248915039⟩, ⟨116209199091, 124343229673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 166461440 167772160 237240320 240189440 ⟨⟨117965888019, 117965888023⟩, ⟨113958039846, 122027914225⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 166461440 167772160 240189440 243138560 ⟨⟨119294909980, 119294909982⟩, ⟨115278213402, 123365742818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 165150720 166461440 243138560 249036800 ⟨⟨122250841270, 122250841278⟩, ⟨117283650496, 127301069881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 166461440 167772160 243138560 249036800 ⟨⟨121283729518, 121283729522⟩, ⟨116348301430, 126301410608⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 167772160 237240320 249036800 t = true :=
  ⟨_, (join_su (m := 165150720) (by decide) (join_sr (m := 243138560) (by decide) (join_su (m := 163840000) (by decide) (leaf_ok cell0) (join_sr (m := 240189440) (by decide) (leaf_ok cell1) (leaf_ok cell2))) (join_su (m := 163840000) (by decide) (leaf_ok cell3) (leaf_ok cell4))) (join_sr (m := 243138560) (by decide) (join_su (m := 166461440) (by decide) (join_sr (m := 240189440) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 240189440) (by decide) (leaf_ok cell7) (leaf_ok cell8))) (join_su (m := 166461440) (by decide) (leaf_ok cell9) (leaf_ok cell10))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (181/640 : ℝ) (19/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e3 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

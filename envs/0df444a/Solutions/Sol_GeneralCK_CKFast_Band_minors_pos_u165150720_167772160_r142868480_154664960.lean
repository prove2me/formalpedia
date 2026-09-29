-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u165150720_167772160_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:41:39.977207+00:00
-- url     : https://prove2.me/submissions/d792ef95-1167-4bbb-9487-07e83840aaae

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [63/320, 1/5]`, `ρ ∈ [109/640, 59/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 165150720 165806080 142868480 145817600 ⟨⟨74781786626, 74781786631⟩, ⟨72463026044, 77122266285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 165806080 166461440 142868480 145817600 ⟨⟨74463823160, 74463823167⟩, ⟨72152822694, 76796420587⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 165150720 165806080 145817600 148766720 ⟨⟨76215513864, 76215513868⟩, ⟨73891149445, 78561573758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 165806080 166461440 145817600 148766720 ⟨⟨75892153452, 75892153459⟩, ⟨73575562810, 78230318127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 166461440 167116800 142868480 145817600 ⟨⟨74147335922, 74147335930⟩, ⟨71844045413, 76472102364⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 167116800 167772160 142868480 145817600 ⟨⟨73832311298, 73832311306⟩, ⟨71536681094, 76149297475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 166461440 167116800 145817600 148766720 ⟨⟨75570286650, 75570286656⟩, ⟨73261419668, 77900607293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 167116800 167772160 145817600 148766720 ⟨⟨75249899729, 75249899735⟩, ⟨72948706803, 77572427010⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 165150720 165806080 148766720 151715840 ⟨⟨77645955736, 77645955741⟩, ⟨75316014675, 79997568488⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 165806080 166461440 148766720 151715840 ⟨⟨77317234566, 77317234574⟩, ⟨74995080547, 79660939505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 165150720 165806080 151715840 154664960 ⟨⟨79073137392, 79073137394⟩, ⟨76737646602, 81430275898⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 165806080 166461440 151715840 154664960 ⟨⟨78739091265, 78739091271⟩, ⟨76411400398, 81088309752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 166461440 167116800 148766720 151715840 ⟨⟨76990024006, 76990024012⟩, ⟨74675606964, 79325872256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 167116800 167772160 148766720 151715840 ⟨⟨76664310220, 76664310228⟩, ⟨74357580599, 78992352396⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 166461440 167116800 151715840 154664960 ⟨⟨78406572372, 78406572379⟩, ⟨76086631418, 80747921903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 167116800 167772160 151715840 154664960 ⟨⟨78075566780, 78075566787⟩, ⟨75763326232, 80409097901⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 165150720 167772160 142868480 154664960 t = true :=
  ⟨_, (join_sr (m := 148766720) (by decide) (join_su (m := 166461440) (by decide) (join_sr (m := 145817600) (by decide) (join_su (m := 165806080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 165806080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 145817600) (by decide) (join_su (m := 167116800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 167116800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 166461440) (by decide) (join_sr (m := 151715840) (by decide) (join_su (m := 165806080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 165806080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 151715840) (by decide) (join_su (m := 167116800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 167116800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (63/320 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

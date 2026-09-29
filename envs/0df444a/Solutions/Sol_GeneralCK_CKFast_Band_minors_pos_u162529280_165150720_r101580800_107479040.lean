-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_165150720_r101580800_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:23:37.754528+00:00
-- url     : https://prove2.me/submissions/365ab5b9-6161-4713-8ce4-c7e635e9b176

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 63/320]`, `ρ ∈ [31/256, 41/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 162529280 163184640 101580800 103055360 ⟨⟨54938397566, 54938397572⟩, ⟨53115466011, 56775700973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 162529280 163184640 103055360 104529920 ⟨⟨55692623981, 55692623987⟩, ⟨53867002255, 57532614691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 163184640 163840000 101580800 103055360 ⟨⟨54696661190, 54696661197⟩, ⟨52879266218, 56528349146⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163184640 163840000 103055360 104529920 ⟨⟨55447855247, 55447855254⟩, ⟨53627778338, 57282222460⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 162529280 163184640 104529920 106004480 ⟨⟨56445885446, 56445885453⟩, ⟨54617579832, 58288557131⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 162529280 163184640 106004480 107479040 ⟨⟨57198185827, 57198185834⟩, ⟨55367202577, 59043532186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 163184640 163840000 104529920 106004480 ⟨⟨56198095479, 56198095485⟩, ⟨54375342818, 58035135715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 163184640 163840000 106004480 107479040 ⟨⟨56947385685, 56947385693⟩, ⟨55121963427, 58787092747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 163840000 164495360 101580800 103055360 ⟨⟨54456155729, 54456155737⟩, ⟨52644258292, 56282268036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 163840000 164495360 103055360 104529920 ⟨⟨55204329631, 55204329638⟩, ⟨53389758476, 57033113162⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 164495360 165150720 101580800 103055360 ⟨⟨54216869071, 54216869079⟩, ⟨52410430543, 56037445104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 164495360 165150720 103055360 104529920 ⟨⟨54962034926, 54962034932⟩, ⟨53152930880, 56785274160⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 163840000 164495360 104529920 106004480 ⟨⟨55951560704, 55951560710⟩, ⟨54134321918, 57783009322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 163840000 164495360 106004480 107479040 ⟨⟨56697852688, 56697852694⟩, ⟨54877952327, 58531960290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 164495360 165150720 104529920 106004480 ⟨⟨55706268821, 55706268827⟩, ⟨53894505249, 57532165220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 164495360 165150720 106004480 107479040 ⟨⟨56449574438, 56449574444⟩, ⟨54635157301, 58278121992⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 165150720 101580800 107479040 t = true :=
  ⟨_, (join_su (m := 163840000) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 163184640) (by decide) (join_sr (m := 103055360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 103055360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 163184640) (by decide) (join_sr (m := 106004480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 106004480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 104529920) (by decide) (join_su (m := 164495360) (by decide) (join_sr (m := 103055360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 103055360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 164495360) (by decide) (join_sr (m := 106004480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 106004480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (63/320 : ℝ) →
    rho ∈ Set.Icc (31/256 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e2 : (((101580800 : ℤ) : ℝ) / (D : ℝ)) = (31/256 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

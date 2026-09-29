-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_167772160_r555745280_602931200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:11:57.675766+00:00
-- url     : https://prove2.me/submissions/77c0e630-8ac8-4e34-bcd0-7e16ea7fd32e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 1/5]`, `ρ ∈ [53/80, 23/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 159907840 555745280 567541760 ⟨⟨262900249600, 262900249611⟩, ⟨250958993363, 275120777137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 159907840 162529280 555745280 567541760 ⟨⟨259446486806, 259446486816⟩, ⟨247627719998, 271542467387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157286400 159907840 567541760 579338240 ⟨⟨267585793317, 267585793328⟩, ⟨255589574340, 279858361607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 159907840 162529280 567541760 579338240 ⟨⟨264090241977, 264090241987⟩, ⟨252215781752, 276239148911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 162529280 165150720 555745280 567541760 ⟨⟨256024169990, 256024169995⟩, ⟨244326202872, 267997288923⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 165150720 167772160 555745280 567541760 ⟨⟨252632528084, 252632528093⟩, ⟨241053709080, 264484433865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 162529280 165150720 567541760 579338240 ⟨⟨260625822293, 260625822297⟩, ⟨248871484032, 272652695369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 165150720 167772160 567541760 579338240 ⟨⟨257191777190, 257191777200⟩, ⟨245555960319, 269098209178⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 157286400 159907840 579338240 591134720 ⟨⟨272252103419, 272252103429⟩, ⟨260201382200, 284576233252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 159907840 162529280 579338240 591134720 ⟨⟨268715331489, 268715331499⟩, ⟨256785626193, 280916696336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 157286400 159907840 591134720 602931200 ⟨⟨276899807461, 276899807471⟩, ⟨264795025573, 289275038336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 159907840 162529280 591134720 602931200 ⟨⟨273322359496, 273322359507⟩, ⟨261337839344, 285575731760⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 162529280 165150720 579338240 591134720 ⟨⟨265209367122, 265209367128⟩, ⟨253399093490, 277289537259⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 165150720 167772160 579338240 591134720 ⟨⟨261733467144, 261733467154⟩, ⟨250041075232, 273693980130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 162529280 165150720 591134720 602931200 ⟨⟨269775385927, 269775385932⟩, ⟨257909595336, 281908413233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 165150720 167772160 591134720 602931200 ⟨⟨266258157363, 266258157373⟩, ⟨254509596639, 278272322593⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 167772160 555745280 602931200 t = true :=
  ⟨_, (join_sr (m := 579338240) (by decide) (join_su (m := 162529280) (by decide) (join_sr (m := 567541760) (by decide) (join_su (m := 159907840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 159907840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 567541760) (by decide) (join_su (m := 165150720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 165150720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 162529280) (by decide) (join_sr (m := 591134720) (by decide) (join_su (m := 159907840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 159907840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 591134720) (by decide) (join_su (m := 165150720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 165150720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (53/80 : ℝ) (23/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((555745280 : ℤ) : ℝ) / (D : ℝ)) = (53/80 : ℝ) := by norm_num [D]
  have e3 : (((602931200 : ℤ) : ℝ) / (D : ℝ)) = (23/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

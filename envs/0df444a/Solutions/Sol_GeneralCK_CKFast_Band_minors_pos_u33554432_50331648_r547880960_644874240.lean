-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_50331648_r547880960_644874240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:56:43.480715+00:00
-- url     : https://prove2.me/submissions/df8c6b2e-be5b-4f7d-abde-0f2bb332b9be

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 3/50]`, `ρ ∈ [209/320, 123/160]` by 17 cells of the computing
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
theorem cell0 : cellOK 33554432 37748736 547880960 572129280 ⟨⟨484314688081, 484314688100⟩, ⟨447176369229, 522339390050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 37748736 41943040 547880960 572129280 ⟨⟨473376948298, 473376948314⟩, ⟨437133798988, 510541307540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 33554432 37748736 572129280 596377600 ⟨⟨496115296015, 496115296031⟩, ⟨459369376548, 533628018941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 37748736 41943040 572129280 596377600 ⟨⟨485227021389, 485227021407⟩, ⟨449327368821, 521933682494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 41943040 46137344 547880960 572129280 ⟨⟨462858572076, 462858572094⟩, ⟨427464624268, 499201011930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 46137344 50331648 547880960 560005120 ⟨⟨449714980029, 449714980044⟩, ⟨423117863080, 476915353307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 46137344 50331648 560005120 572129280 ⟨⟨455712721223, 455712721238⟩, ⟨429194218237, 482803825239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 41943040 46137344 572129280 596377600 ⟨⟨474741057638, 474741057653⟩, ⟨439645549963, 510676133325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 46137344 50331648 572129280 596377600 ⟨⟨464619601938, 464619601953⟩, ⟨430291521788, 499813681923⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 33554432 37748736 596377600 620625920 ⟨⟨507738923878, 507738923894⟩, ⟨471366380501, 544766569454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 37748736 41943040 596377600 620625920 ⟨⟨496898563132, 496898563149⟩, ⟨461326572265, 533170520446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 33554432 37748736 620625920 644874240 ⟨⟨519204232264, 519204232280⟩, ⟨483187099109, 555771690430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 37748736 41943040 620625920 644874240 ⟨⟨508410023879, 508410023895⟩, ⟨473150611570, 544268676100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 41943040 46137344 596377600 620625920 ⟨⟨486444497019, 486444497034⟩, ⟨451634393734, 521991733438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 46137344 50331648 596377600 620625920 ⟨⟨476340481858, 476340481873⟩, ⟨442258674707, 511190387942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 41943040 46137344 620625920 644874240 ⟨⟨497987037499, 497987037516⟩, ⟨463449799407, 533164718644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 46137344 50331648 620625920 644874240 ⟨⟨487900452338, 487900452353⟩, ⟨454054623485, 522421690243⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 50331648 547880960 644874240 t = true :=
  ⟨_, (join_sr (m := 596377600) (by decide) (join_su (m := 41943040) (by decide) (join_sr (m := 572129280) (by decide) (join_su (m := 37748736) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 37748736) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 572129280) (by decide) (join_su (m := 46137344) (by decide) (leaf_ok cell4) (join_sr (m := 560005120) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 46137344) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_su (m := 41943040) (by decide) (join_sr (m := 620625920) (by decide) (join_su (m := 37748736) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 37748736) (by decide) (leaf_ok cell11) (leaf_ok cell12))) (join_sr (m := 620625920) (by decide) (join_su (m := 46137344) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_su (m := 46137344) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (209/320 : ℝ) (123/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((547880960 : ℤ) : ℝ) / (D : ℝ)) = (209/320 : ℝ) := by norm_num [D]
  have e3 : (((644874240 : ℤ) : ℝ) / (D : ℝ)) = (123/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

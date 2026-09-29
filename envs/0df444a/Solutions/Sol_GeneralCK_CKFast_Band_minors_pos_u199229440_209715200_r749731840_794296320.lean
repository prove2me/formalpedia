-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_209715200_r749731840_794296320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:11:07.253748+00:00
-- url     : https://prove2.me/submissions/df8ae7eb-bee0-4306-8f72-9e741cf2e505

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 1/4]`, `ρ ∈ [143/160, 303/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 201850880 749731840 760872960 ⟨⟨275212771757, 275212771767⟩, ⟨264242878857, 286402669775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 201850880 204472320 749731840 760872960 ⟨⟨271479072339, 271479072343⟩, ⟨260602861035, 282574862316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 199229440 201850880 760872960 772014080 ⟨⟨278838271612, 278838271622⟩, ⟨267813628382, 290081659099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 201850880 204472320 760872960 772014080 ⟨⟨275066483093, 275066483098⟩, ⟨264135287626, 286216083027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 204472320 207093760 749731840 760872960 ⟨⟨267763382877, 267763382886⟩, ⟨256980168639, 278765714569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 207093760 209715200 749731840 760872960 ⟨⟨264065329522, 264065329532⟩, ⟨253374436397, 274974845363⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 204472320 207093760 760872960 772014080 ⟨⟨271312459218, 271312459228⟩, ⟨260474054755, 282368891466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 207093760 209715200 760872960 772014080 ⟨⟨267575832816, 267575832826⟩, ⟨256829570484, 278539710643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 199229440 201850880 772014080 783155200 ⟨⟨282457955871, 282457955881⟩, ⟨271378665781, 293754703477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 201850880 204472320 772014080 783155200 ⟨⟨278648269871, 278648269876⟩, ⟨267662187175, 289851557207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 199229440 201850880 783155200 794296320 ⟨⟨286072046506, 286072046516⟩, ⟨274938207581, 297422030058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 201850880 204472320 783155200 794296320 ⟨⟨282224646345, 282224646350⟩, ⟨271183768148, 293481503474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 204472320 207093760 772014080 783155200 ⟨⟨274856099746, 274856099757⟩, ⟨263962595421, 285966516867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 207093760 209715200 772014080 783155200 ⟨⟨271081084970, 271081084980⟩, ⟨260279537205, 282099216021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 204472320 207093760 783155200 794296320 ⟨⟨278394510051, 278394510061⟩, ⟨267445991256, 289558801075⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 207093760 209715200 783155200 794296320 ⟨⟨274581283699, 274581283711⟩, ⟨263724529537, 285653563703⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 209715200 749731840 794296320 t = true :=
  ⟨_, (join_sr (m := 772014080) (by decide) (join_su (m := 204472320) (by decide) (join_sr (m := 760872960) (by decide) (join_su (m := 201850880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 201850880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 760872960) (by decide) (join_su (m := 207093760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 207093760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 204472320) (by decide) (join_sr (m := 783155200) (by decide) (join_su (m := 201850880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 201850880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 783155200) (by decide) (join_su (m := 207093760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 207093760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (143/160 : ℝ) (303/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((749731840 : ℤ) : ℝ) / (D : ℝ)) = (143/160 : ℝ) := by norm_num [D]
  have e3 : (((794296320 : ℤ) : ℝ) / (D : ℝ)) = (303/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

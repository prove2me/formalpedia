-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_141557760_r154664960_166461440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:33:15.213918+00:00
-- url     : https://prove2.me/submissions/7839c6eb-01fb-49b3-8c71-d5f233256129

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 27/160]`, `ρ ∈ [59/320, 127/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 137625600 154664960 157614080 ⟨⟨96990965509, 96990965518⟩, ⟨92645069105, 101407590451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136314880 137625600 157614080 160563200 ⟨⟨98657103181, 98657103190⟩, ⟨94300600830, 103084207965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 137625600 138936320 154664960 157614080 ⟨⟨96147334134, 96147334143⟩, ⟨91831922619, 100532641987⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 137625600 138936320 157614080 160563200 ⟨⟨97801407035, 97801407042⟩, ⟨93475415878, 102197174613⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 136314880 137625600 160563200 163512320 ⟨⟨100318133578, 100318133585⟩, ⟨95951097009, 104755645807⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 136314880 137625600 163512320 166461440 ⟨⟨101974104073, 101974104082⟩, ⟨97596604095, 106421952280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 137625600 138936320 160563200 163512320 ⟨⟨99450481819, 99450481828⟩, ⟨95113980870, 103856638600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 137625600 138936320 163512320 166461440 ⟨⟨101094604410, 101094604417⟩, ⟨96747662634, 105511080759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 138936320 140247040 154664960 157614080 ⟨⟨95313045092, 95313045100⟩, ⟨91027647782, 99667523239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 138936320 140247040 157614080 160563200 ⟨⟨96955134127, 96955134134⟩, ⟨92659184729, 101320050421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 140247040 141557760 154664960 157614080 ⟨⟨94487906256, 94487906262⟩, ⟨90232063374, 98812030719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 140247040 141557760 157614080 160563200 ⟨⟨96118091477, 96118091483⟩, ⟨91851725240, 100452631121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 138936320 140247040 160563200 163512320 ⟨⟨98592331879, 98592331886⟩, ⟨94285898404, 102967617626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 138936320 140247040 163512320 166461440 ⟨⟨100224682858, 100224682867⟩, ⟨95907832473, 104610270223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 140247040 141557760 160563200 163512320 ⟨⟨97743489974, 97743489979⟩, ⟨93466666597, 102088377899⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 140247040 141557760 163512320 166461440 ⟨⟨99364144895, 99364144900⟩, ⟨95076929780, 103719315020⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 141557760 154664960 166461440 t = true :=
  ⟨_, (join_su (m := 138936320) (by decide) (join_sr (m := 160563200) (by decide) (join_su (m := 137625600) (by decide) (join_sr (m := 157614080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 157614080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 137625600) (by decide) (join_sr (m := 163512320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 163512320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 160563200) (by decide) (join_su (m := 140247040) (by decide) (join_sr (m := 157614080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 157614080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 140247040) (by decide) (join_sr (m := 163512320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 163512320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (27/160 : ℝ) →
    rho ∈ Set.Icc (59/320 : ℝ) (127/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e2 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e3 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

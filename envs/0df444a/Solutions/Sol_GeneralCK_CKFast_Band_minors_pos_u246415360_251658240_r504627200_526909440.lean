-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_251658240_r504627200_526909440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:29:28.617995+00:00
-- url     : https://prove2.me/submissions/d1373c79-d8f2-4d89-bd57-ef80f93e9c4b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 3/10]`, `ρ ∈ [77/128, 201/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247726080 504627200 510197760 ⟨⟨145437552246, 145437552253⟩, ⟨141326899712, 149599284534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 247726080 249036800 504627200 510197760 ⟨⟨144188356556, 144188356564⟩, ⟨140097200409, 148330352438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246415360 247726080 510197760 515768320 ⟨⟨146944200963, 146944200971⟩, ⟨142819612072, 151119911900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247726080 249036800 510197760 515768320 ⟨⟨145683533244, 145683533251⟩, ⟨141578479935, 149839471103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249036800 250347520 504627200 510197760 ⟨⟨142942807252, 142942807258⟩, ⟨138871034138, 147065181327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 250347520 251658240 504627200 510197760 ⟨⟨141700860760, 141700860768⟩, ⟨137648358438, 145803726507⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249036800 250347520 510197760 515768320 ⟨⟨144426509360, 144426509368⟩, ⟨140340879094, 148562787874⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 250347520 251658240 510197760 515768320 ⟨⟨143173085893, 143173085901⟩, ⟨139106767225, 147289817691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 246415360 247726080 515768320 521338880 ⟨⟨148449461080, 148449461088⟩, ⟨144310941253, 152639144349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 247726080 249036800 515768320 521338880 ⟨⟨147177353801, 147177353808⟩, ⟨143058408187, 151347227903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 246415360 247726080 521338880 526909440 ⟨⟨149953348421, 149953348429⟩, ⟨145800902951, 154156997833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 247726080 249036800 521338880 526909440 ⟨⟨148669833635, 148669833641⟩, ⟨144537000450, 152853638370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249036800 250347520 515768320 521338880 ⟨⟨145908887281, 145908887288⟩, ⟨141809404163, 150059065073⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250347520 251658240 515768320 521338880 ⟨⟨144644018253, 144644018261⟩, ⟨140563886995, 148774611504⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 249036800 250347520 521338880 526909440 ⟨⟨147389956009, 147389956015⟩, ⟨143276624225, 151554028033⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250347520 251658240 521338880 526909440 ⟨⟨146113672436, 146113672443⟩, ⟨142019732234, 150258122651⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 251658240 504627200 526909440 t = true :=
  ⟨_, (join_sr (m := 515768320) (by decide) (join_su (m := 249036800) (by decide) (join_sr (m := 510197760) (by decide) (join_su (m := 247726080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 247726080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 510197760) (by decide) (join_su (m := 250347520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 250347520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 249036800) (by decide) (join_sr (m := 521338880) (by decide) (join_su (m := 247726080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 247726080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 521338880) (by decide) (join_su (m := 250347520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 250347520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (77/128 : ℝ) (201/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((504627200 : ℤ) : ℝ) / (D : ℝ)) = (77/128 : ℝ) := by norm_num [D]
  have e3 : (((526909440 : ℤ) : ℝ) / (D : ℝ)) = (201/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_136314880_r343408640_367001600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:44:34.526553+00:00
-- url     : https://prove2.me/submissions/cac59b6e-b4e8-4ad1-93fc-88b3a996e742

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 13/80]`, `ρ ∈ [131/320, 7/16]` by 16 cells of the computing
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
theorem cell0 : cellOK 125829120 128450560 343408640 349306880 ⟨⟨206955136248, 206955136258⟩, ⟨196724811545, 217446557371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 125829120 128450560 349306880 355205120 ⟨⟨209889816845, 209889816856⟩, ⟨199631229188, 220407941423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 128450560 131072000 343408640 349306880 ⟨⟨203890146373, 203890146384⟩, ⟨193787287378, 214250080071⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 128450560 131072000 349306880 355205120 ⟨⟨206796161446, 206796161456⟩, ⟨196664575965, 217183361118⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 125829120 128450560 355205120 361103360 ⟨⟨212811488783, 212811488794⟩, ⟨202524929952, 223356024475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 125829120 128450560 361103360 367001600 ⟨⟨215720381359, 215720381370⟩, ⟨205406135959, 226291043061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 128450560 131072000 355205120 361103360 ⟨⟨209689589335, 209689589346⟩, ⟨199529560959, 220103769922⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 128450560 131072000 361103360 367001600 ⟨⟨212570648845, 212570648855⟩, ⟨202382454367, 223011532156⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 131072000 133693440 343408640 349306880 ⟨⟨200875445194, 200875445204⟩, ⟨190896959754, 211107084463⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 131072000 133693440 349306880 355205120 ⟨⟨203752716537, 203752716548⟩, ⟨193745082577, 214012137996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 133693440 136314880 343408640 349306880 ⟨⟨197909365182, 197909365192⟩, ⟨188052274337, 208015786745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 133693440 136314880 349306880 355205120 ⟨⟨200757828170, 200757828180⟩, ⟨190871205807, 210892504548⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 131072000 133693440 355205120 361103360 ⟨⟨206617811534, 206617811545⟩, ⟨196581304318, 216904737645⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 131072000 133693440 361103360 367001600 ⟨⟨209470938949, 209470938960⟩, ⟨199405827309, 219785098682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 133693440 136314880 355205120 361103360 ⟨⟨203594515148, 203594515157⟩, ⟨193678628111, 213757176515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 133693440 136314880 361103360 367001600 ⟨⟨206419625276, 206419625285⟩, ⟨196474734329, 216610007965⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 136314880 343408640 367001600 t = true :=
  ⟨_, (join_su (m := 131072000) (by decide) (join_sr (m := 355205120) (by decide) (join_su (m := 128450560) (by decide) (join_sr (m := 349306880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 349306880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 128450560) (by decide) (join_sr (m := 361103360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 361103360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 355205120) (by decide) (join_su (m := 133693440) (by decide) (join_sr (m := 349306880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 349306880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 133693440) (by decide) (join_sr (m := 361103360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 361103360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (131/320 : ℝ) (7/16 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((343408640 : ℤ) : ℝ) / (D : ℝ)) = (131/320 : ℝ) := by norm_num [D]
  have e3 : (((367001600 : ℤ) : ℝ) / (D : ℝ)) = (7/16 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

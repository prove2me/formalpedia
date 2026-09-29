-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_235929600_r370933760_393216000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:55:20.046305+00:00
-- url     : https://prove2.me/submissions/468c6f19-8292-4c45-87ad-75199a757e5e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 9/32]`, `ρ ∈ [283/640, 15/32]` by 17 cells of the computing
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
theorem cell0 : cellOK 230686720 231997440 370933760 376504320 ⟨⟨120666527151, 120666527157⟩, ⟨116661211816, 124725396813⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 231997440 233308160 370933760 376504320 ⟨⟨119657528322, 119657528326⟩, ⟨115672260545, 123696022543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 230686720 231997440 376504320 382074880 ⟨⟨122361143715, 122361143722⟩, ⟨118341111975, 126434763126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231997440 233308160 376504320 382074880 ⟨⟨121339600057, 121339600059⟩, ⟨117339663125, 125392799576⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 233308160 234618880 370933760 376504320 ⟨⟨118652642730, 118652642736⟩, ⟨114687273266, 122670913682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 234618880 235929600 370933760 373719040 ⟨⟨117237211884, 117237211890⟩, ⟨113834605019, 120677714789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 234618880 235929600 373719040 376504320 ⟨⟨118066282903, 118066282910⟩, ⟨114656843065, 121513648245⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 233308160 234618880 376504320 382074880 ⟨⟨120322182785, 120322182793⟩, ⟨116342192138, 124355113803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 234618880 235929600 376504320 382074880 ⟨⟨119308839209, 119308839215⟩, ⟨115348648104, 123321651279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 230686720 231997440 382074880 387645440 ⟨⟨124053376643, 124053376651⟩, ⟨120018647024, 128141726224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 231997440 233308160 382074880 387645440 ⟨⟨123019341982, 123019341986⟩, ⟨119004753507, 127087228157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 230686720 231997440 387645440 393216000 ⟨⟨125743251236, 125743251242⟩, ⟨121693842015, 129846311645⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 231997440 233308160 387645440 393216000 ⟨⟨124696778715, 124696778718⟩, ⟨120667556069, 128779333133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 233308160 234618880 382074880 387645440 ⟨⟨121989445955, 121989445962⟩, ⟨117994850832, 126037019311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 234618880 235929600 382074880 387645440 ⟨⟨120963635900, 120963635907⟩, ⟨116988888103, 124991045213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 233308160 234618880 387645440 393216000 ⟨⟨123654456184, 123654456191⟩, ⟨119645273070, 127716654375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 234618880 235929600 387645440 393216000 ⟨⟨122616231024, 122616231031⟩, ⟨118626942146, 126658220969⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 235929600 370933760 393216000 t = true :=
  ⟨_, (join_sr (m := 382074880) (by decide) (join_su (m := 233308160) (by decide) (join_sr (m := 376504320) (by decide) (join_su (m := 231997440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 231997440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 376504320) (by decide) (join_su (m := 234618880) (by decide) (leaf_ok cell4) (join_sr (m := 373719040) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 234618880) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_su (m := 233308160) (by decide) (join_sr (m := 387645440) (by decide) (join_su (m := 231997440) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 231997440) (by decide) (leaf_ok cell11) (leaf_ok cell12))) (join_sr (m := 387645440) (by decide) (join_su (m := 234618880) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_su (m := 234618880) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (283/640 : ℝ) (15/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  have e3 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

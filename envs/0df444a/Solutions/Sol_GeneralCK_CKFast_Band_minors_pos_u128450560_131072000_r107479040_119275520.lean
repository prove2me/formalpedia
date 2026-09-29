-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u128450560_131072000_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:02:20.451467+00:00
-- url     : https://prove2.me/submissions/f487cb14-a6d7-44e7-8efc-e46923d95e68

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [49/320, 5/32]`, `ρ ∈ [41/320, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 128450560 129105920 107479040 110428160 ⟨⟨73748163832, 73748163840⟩, ⟨70974462191, 76553725743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 129105920 129761280 107479040 110428160 ⟨⟨73403694899, 73403694900⟩, ⟨70641525270, 76197490262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 128450560 129105920 110428160 113377280 ⟨⟨75593606735, 75593606742⟩, ⟨72812922963, 78406064767⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 129105920 129761280 110428160 113377280 ⟨⟨75241689358, 75241689362⟩, ⟨72472553844, 78042366458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 129761280 130416640 107479040 110428160 ⟨⟨73061470147, 73061470154⟩, ⟨70310735025, 75843599213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 130416640 131072000 107479040 110428160 ⟨⟨72721463349, 72721463356⟩, ⟨69982066494, 75492025035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 129761280 130416640 110428160 113377280 ⟨⟨74892051153, 74892051161⟩, ⟨72134366551, 77681047367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 130416640 131072000 110428160 113377280 ⟨⟨74544665604, 74544665613⟩, ⟨71798335835, 77322079659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 128450560 129105920 113377280 116326400 ⟨⟨77432172337, 77432172346⟩, ⟨74644577214, 80251455549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 129105920 129761280 113377280 116326400 ⟨⟨77072886242, 77072886245⟩, ⟨74296854598, 79880375149⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 128450560 129105920 116326400 119275520 ⟨⟨79263931711, 79263931718⟩, ⟨76469494921, 82089970259⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 129105920 129761280 116326400 119275520 ⟨⟨78897355415, 78897355419⟩, ⟨76114496332, 81711587280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 129761280 130416640 113377280 116326400 ⟨⟨76715913325, 76715913332⟩, ⟨73951347994, 79511707761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 130416640 131072000 113377280 116326400 ⟨⟨76361226802, 76361226809⟩, ⟨73608031876, 79145425286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 129761280 130416640 116326400 119275520 ⟨⟨78533125346, 78533125354⟩, ⟨75761746993, 81335650134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 130416640 131072000 116326400 119275520 ⟨⟨78171214463, 78171214472⟩, ⟨75411221119, 80962130474⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 128450560 131072000 107479040 119275520 t = true :=
  ⟨_, (join_sr (m := 113377280) (by decide) (join_su (m := 129761280) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 129105920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 129105920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 110428160) (by decide) (join_su (m := 130416640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 130416640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 129761280) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 129105920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 129105920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 116326400) (by decide) (join_su (m := 130416640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 130416640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (49/320 : ℝ) (5/32 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((128450560 : ℤ) : ℝ) / (D : ℝ)) = (49/320 : ℝ) := by norm_num [D]
  have e1 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

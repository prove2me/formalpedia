-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_249036800_r198246400_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:23:13.90583+00:00
-- url     : https://prove2.me/submissions/a2db299c-185b-423d-9128-d3352e18800d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 19/64]`, `ρ ∈ [121/512, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247070720 198246400 199639040 ⟨⟨59463999806, 59463999811⟩, ⟨58026639849, 60909800635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246415360 247070720 199639040 201031680 ⟨⟨59867893409, 59867893414⟩, ⟨58428848184, 61315385221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247070720 247726080 198246400 199639040 ⟨⟨59188817329, 59188817333⟩, ⟨57754349670, 60631700004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247070720 247726080 199639040 201031680 ⟨⟨59590949347, 59590949351⟩, ⟨58154800638, 61035518813⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 246415360 247070720 201031680 202424320 ⟨⟨60271633371, 60271633377⟩, ⟨58830903100, 61720815935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246415360 247070720 202424320 203816960 ⟨⟨60675220047, 60675220052⟩, ⟨59232804952, 62126093132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247070720 247726080 201031680 202424320 ⟨⟨59992929717, 59992929718⟩, ⟨58555100166, 61439185755⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247070720 247726080 202424320 203816960 ⟨⟨60394758782, 60394758786⟩, ⟨58955248602, 61842701174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 247726080 248381440 198246400 199639040 ⟨⟨58914300688, 58914300693⟩, ⟨57482712237, 60354278456⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 247726080 248381440 199639040 201031680 ⟨⟨59314673992, 59314673997⟩, ⟨57881408706, 60756334362⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 248381440 249036800 198246400 199639040 ⟨⟨58640445098, 58640445103⟩, ⟨57211722857, 60077531113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 248381440 249036800 199639040 201031680 ⟨⟨59039062541, 59039062547⟩, ⟨57608667677, 60477826972⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 247726080 248381440 201031680 202424320 ⟨⟨59714897615, 59714897622⟩, ⟨58279955694, 61158240381⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 247726080 248381440 202424320 203816960 ⟨⟨60114971903, 60114971908⟩, ⟨58678353542, 61559996857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 248381440 249036800 201031680 202424320 ⟨⟨59437532255, 59437532262⟩, ⟨58005464955, 60877974907⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 248381440 249036800 202424320 203816960 ⟨⟨59835854577, 59835854583⟩, ⟨58402115025, 61277975256⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 249036800 198246400 203816960 t = true :=
  ⟨_, (join_su (m := 247726080) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 247070720) (by decide) (join_sr (m := 199639040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 199639040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 247070720) (by decide) (join_sr (m := 202424320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 202424320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 201031680) (by decide) (join_su (m := 248381440) (by decide) (join_sr (m := 199639040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 199639040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 248381440) (by decide) (join_sr (m := 202424320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 202424320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (121/512 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((198246400 : ℤ) : ℝ) / (D : ℝ)) = (121/512 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

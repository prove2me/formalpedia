-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u217579520_220200960_r175964160_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:33:57.419506+00:00
-- url     : https://prove2.me/submissions/5193695e-5c03-44b8-affd-70735e978e84

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [83/320, 21/80]`, `ρ ∈ [537/2560, 277/1280]` by 13 cells of the computing
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
theorem cell0 : cellOK 217579520 218234880 175964160 177356800 ⟨⟨64522415784, 64522415787⟩, ⟨62973407067, 66081112853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 217579520 218234880 177356800 178749440 ⟨⟨65011244756, 65011244759⟩, ⟨63460347557, 66571834589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 218234880 218890240 175964160 177356800 ⟨⟨64243483217, 64243483224⟩, ⟨62697974633, 65798645143⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 218234880 218890240 177356800 178749440 ⟨⟨64730356422, 64730356428⟩, ⟨63182963979, 66287406539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 217579520 218234880 178749440 181534720 ⟨⟨65743971236, 65743971239⟩, ⟨63900908590, 67601107431⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 218234880 218890240 178749440 181534720 ⟨⟨65460155368, 65460155373⟩, ⟨63622016714, 67312308457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 218890240 219545600 175964160 177356800 ⟨⟨63965406848, 63965406853⟩, ⟨62423380390, 65517051875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 218890240 219545600 177356800 178749440 ⟨⟨64450328433, 64450328440⟩, ⟨62906422734, 66003857079⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 219545600 220200960 175964160 177356800 ⟨⟨63688180185, 63688180192⟩, ⟨62149617985, 65236326417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 219545600 220200960 177356800 178749440 ⟨⟨64171154274, 64171154281⟩, ⟨62630717449, 65721179557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 218890240 219545600 178749440 181534720 ⟨⟨65177206004, 65177206010⟩, ⟨63343967571, 67024400153⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 219545600 220200960 178749440 180142080 ⟨⟨64653862215, 64653862222⟩, ⟨63111551702, 66205765596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 219545600 220200960 180142080 181534720 ⟨⟨65136304702, 65136304707⟩, ⟨63592121435, 66690085230⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 217579520 220200960 175964160 181534720 t = true :=
  ⟨_, (join_su (m := 218890240) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 218234880) (by decide) (join_sr (m := 177356800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 177356800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 218234880) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 178749440) (by decide) (join_su (m := 219545600) (by decide) (join_sr (m := 177356800) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 177356800) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 219545600) (by decide) (leaf_ok cell10) (join_sr (m := 180142080) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (83/320 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (537/2560 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((175964160 : ℤ) : ℝ) / (D : ℝ)) = (537/2560 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

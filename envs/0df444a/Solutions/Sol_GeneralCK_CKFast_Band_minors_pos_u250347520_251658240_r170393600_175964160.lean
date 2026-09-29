-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u250347520_251658240_r170393600_175964160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:09:25.632822+00:00
-- url     : https://prove2.me/submissions/e049b7e1-ee41-4dd1-925c-373e01a943ca

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [191/640, 3/10]`, `ρ ∈ [13/64, 537/2560]` by 15 cells of the computing
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
theorem cell0 : cellOK 250347520 250675200 170393600 171786240 ⟨⟨49984224337, 49984224343⟩, ⟨49176743290, 50794584160⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 250675200 251002880 170393600 171786240 ⟨⟨49866096320, 49866096326⟩, ⟨49059594066, 50675471931⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 250347520 250675200 171786240 173178880 ⟨⟨50380945634, 50380945641⟩, ⟨49572568796, 51192202726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 250675200 251002880 171786240 173178880 ⟨⟨50261925261, 50261925266⟩, ⟨49454528548, 51072196812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 251002880 251330560 170393600 171786240 ⟨⟨49748113593, 49748113599⟩, ⟨48942588067, 50556507074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 251330560 251658240 170393600 171786240 ⟨⟨49630275625, 49630275629⟩, ⟨48825724772, 50437689044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 251002880 251330560 171786240 173178880 ⟨⟨50143050975, 50143050980⟩, ⟨49336632323, 50952339068⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 251330560 251658240 171786240 173178880 ⟨⟨50024322243, 50024322247⟩, ⟨49218879595, 50832628949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 250347520 250675200 173178880 174571520 ⟨⟨50777517904, 50777517909⟩, ⟨49968245454, 51589672078⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 250675200 251002880 173178880 174571520 ⟨⟨50657606166, 50657606171⟩, ⟨49849315173, 51468773475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 250347520 251002880 174571520 175964160 ⟨⟨51113521930, 51113521933⟩, ⟨49721564873, 52513666115⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 251002880 251330560 173178880 174571520 ⟨⟨50537841310, 50537841315⟩, ⟨49730529705, 51348023837⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 251330560 251658240 173178880 174571520 ⟨⟨50418222799, 50418222800⟩, ⟨49611888525, 51227422616⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 251002880 251330560 174571520 175964160 ⟨⟨50932484924, 50932484930⟩, ⟨50124280542, 51743561710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 251330560 251658240 174571520 175964160 ⟨⟨50811977613, 50811977617⟩, ⟨50004751887, 51622070370⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 250347520 251658240 170393600 175964160 t = true :=
  ⟨_, (join_sr (m := 173178880) (by decide) (join_su (m := 251002880) (by decide) (join_sr (m := 171786240) (by decide) (join_su (m := 250675200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 250675200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 171786240) (by decide) (join_su (m := 251330560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 251330560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 251002880) (by decide) (join_sr (m := 174571520) (by decide) (join_su (m := 250675200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 174571520) (by decide) (join_su (m := 251330560) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 251330560) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (191/640 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (537/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((250347520 : ℤ) : ℝ) / (D : ℝ)) = (191/640 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((175964160 : ℤ) : ℝ) / (D : ℝ)) = (537/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

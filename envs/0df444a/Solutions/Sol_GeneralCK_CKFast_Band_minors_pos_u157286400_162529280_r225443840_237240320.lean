-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_162529280_r225443840_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:56:03.366664+00:00
-- url     : https://prove2.me/submissions/6768e965-b7fb-46c8-909b-6561f5c22bd3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 31/160]`, `ρ ∈ [43/160, 181/640]` by 14 cells of the computing
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
theorem cell0 : cellOK 157286400 158597120 225443840 228392960 ⟨⟨119150010101, 119150010108⟩, ⟨115011151023, 123346715783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157286400 158597120 228392960 231342080 ⟨⟨120553113987, 120553113994⟩, ⟨116405175964, 124758835523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 158597120 159907840 225443840 228392960 ⟨⟨118194323961, 118194323968⟩, ⟨114080187101, 122365782430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 158597120 159907840 228392960 231342080 ⟨⟨119588203459, 119588203466⟩, ⟨115465000728, 123768668348⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 157286400 158597120 231342080 237240320 ⟨⟨122652174797, 122652174806⟩, ⟨117525605851, 127867339684⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 158597120 159907840 231342080 237240320 ⟨⟨121673539380, 121673539387⟩, ⟨116581028348, 126853762069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 159907840 161218560 225443840 228392960 ⟨⟨117246673501, 117246673503⟩, ⟨113156946666, 121393205251⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 159907840 161218560 228392960 231342080 ⟨⟨118631364255, 118631364259⟩, ⟨114532585625, 122786891885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 161218560 162529280 225443840 228392960 ⟨⟨116306921495, 116306921502⟩, ⟨112241298428, 120428840922⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 161218560 162529280 228392960 231342080 ⟨⟨117682459017, 117682459024⟩, ⟨113607799184, 121813362722⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 159907840 161218560 231342080 234291200 ⟨⟨120013185413, 120013185419⟩, ⟨115905389489, 124177673894⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 159907840 161218560 234291200 237240320 ⟨⟨121392158865, 121392158870⟩, ⟨117275379817, 125565573497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 161218560 162529280 231342080 234291200 ⟨⟨119055184486, 119055184493⟩, ⟨114971521510, 123195038320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 161218560 162529280 234291200 237240320 ⟨⟨120425119185, 120425119192⟩, ⟨116332486373, 124573889322⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 162529280 225443840 237240320 t = true :=
  ⟨_, (join_su (m := 159907840) (by decide) (join_sr (m := 231342080) (by decide) (join_su (m := 158597120) (by decide) (join_sr (m := 228392960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 228392960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 158597120) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 231342080) (by decide) (join_su (m := 161218560) (by decide) (join_sr (m := 228392960) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 228392960) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 161218560) (by decide) (join_sr (m := 234291200) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 234291200) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (43/160 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

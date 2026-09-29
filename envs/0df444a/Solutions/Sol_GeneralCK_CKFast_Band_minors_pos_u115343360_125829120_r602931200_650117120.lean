-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_125829120_r602931200_650117120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:51:38.342588+00:00
-- url     : https://prove2.me/submissions/c1649157-7f3f-488b-91f0-af806516fe8b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 3/20]`, `ρ ∈ [23/32, 31/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 115343360 117964800 602931200 614727680 ⟨⟨344194579897, 344194579908⟩, ⟨329893329288, 358781328142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 117964800 120586240 602931200 614727680 ⟨⟨339975273125, 339975273137⟩, ⟨325822368742, 354412957494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 115343360 117964800 614727680 626524160 ⟨⟨349380233058, 349380233069⟩, ⟨335046787664, 363993129277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 117964800 120586240 614727680 626524160 ⟨⟨345129266683, 345129266695⟩, ⟨330942278893, 359595218317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 120586240 123207680 602931200 614727680 ⟨⟨335801527689, 335801527701⟩, ⟨321794820482, 350092224019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 123207680 125829120 602931200 614727680 ⟨⟨331672089535, 331672089542⟩, ⟨317809485499, 345817823482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 120586240 123207680 614727680 626524160 ⟨⟨340923195129, 340923195141⟩, ⟨326880605493, 355244182607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 123207680 125829120 614727680 626524160 ⟨⟨336760791427, 336760791434⟩, ⟨322860592362, 350938748260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 115343360 117964800 626524160 638320640 ⟨⟨354540640642, 354540640654⟩, ⟨340175408963, 369179305010⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 117964800 120586240 626524160 638320640 ⟨⟨350258570140, 350258570153⟩, ⟨336037917153, 364752394428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 115343360 117964800 638320640 650117120 ⟨⟨359676783841, 359676783855⟩, ⟨345280148115, 374340860908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 117964800 120586240 638320640 650117120 ⟨⟨355364134927, 355364134940⟩, ⟨341110209117, 369885461395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 120586240 123207680 626524160 638320640 ⟨⟨346020726596, 346020726608⟩, ⟨331942680417, 360371598194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 123207680 125829120 626524160 638320640 ⟨⟨341825909476, 341825909480⟩, ⟨327888547055, 356035671966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 120586240 123207680 638320640 650117120 ⟨⟨351095044323, 351095044336⟩, ⟨336981942122, 365475416853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 123207680 125829120 638320640 650117120 ⟨⟨346868337290, 346868337298⟩, ⟨332894218337, 361109511693⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 125829120 602931200 650117120 t = true :=
  ⟨_, (join_sr (m := 626524160) (by decide) (join_su (m := 120586240) (by decide) (join_sr (m := 614727680) (by decide) (join_su (m := 117964800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 117964800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 614727680) (by decide) (join_su (m := 123207680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 123207680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 120586240) (by decide) (join_sr (m := 638320640) (by decide) (join_su (m := 117964800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 117964800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 638320640) (by decide) (join_su (m := 123207680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 123207680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (23/32 : ℝ) (31/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((602931200 : ℤ) : ℝ) / (D : ℝ)) = (23/32 : ℝ) := by norm_num [D]
  have e3 : (((650117120 : ℤ) : ℝ) / (D : ℝ)) = (31/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

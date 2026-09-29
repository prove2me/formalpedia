-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u120586240_125829120_r190054400_201850880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:34:53.942459+00:00
-- url     : https://prove2.me/submissions/2dc1f8d1-354e-4dec-b7a6-b3b166fb46f3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/160, 3/20]`, `ρ ∈ [29/128, 77/320]` by 10 cells of the computing
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
theorem cell0 : cellOK 120586240 121896960 190054400 195952640 ⟨⟨130181348229, 130181348233⟩, ⟨124034345530, 136454840885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 121896960 123207680 190054400 195952640 ⟨⟨129054353922, 129054353930⟩, ⟨122957804341, 135275748687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 120586240 121896960 195952640 201850880 ⟨⟨133654566517, 133654566521⟩, ⟨127486499994, 139948247287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 121896960 123207680 195952640 201850880 ⟨⟨132504744063, 132504744073⟩, ⟨126387052544, 138746437315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 123207680 124518400 190054400 193003520 ⟨⟨127079994286, 127079994295⟩, ⟨122277157101, 131960459986⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 123207680 124518400 193003520 195952640 ⟨⟨128799438002, 128799438012⟩, ⟨123986849191, 133689448493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 124518400 125829120 190054400 193003520 ⟨⟨125984569106, 125984569116⟩, ⟨121217572840, 130828270675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 124518400 125829120 193003520 195952640 ⟨⟨127692596182, 127692596192⟩, ⟨122915832537, 132545866832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 123207680 124518400 195952640 201850880 ⟨⟨131368094335, 131368094342⟩, ⟨125299988923, 137558621283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 124518400 125829120 195952640 201850880 ⟨⟨130244340259, 130244340268⟩, ⟨124225050885, 136384502434⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 120586240 125829120 190054400 201850880 t = true :=
  ⟨_, (join_su (m := 123207680) (by decide) (join_sr (m := 195952640) (by decide) (join_su (m := 121896960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 121896960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 195952640) (by decide) (join_su (m := 124518400) (by decide) (join_sr (m := 193003520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 193003520) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 124518400) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/160 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (29/128 : ℝ) (77/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((190054400 : ℤ) : ℝ) / (D : ℝ)) = (29/128 : ℝ) := by norm_num [D]
  have e3 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

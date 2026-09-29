-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u141557760_146800640_r213647360_225443840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:42:37.539482+00:00
-- url     : https://prove2.me/submissions/599c6797-512c-4d81-9666-068c3a03b72e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [27/160, 7/40]`, `ρ ∈ [163/640, 43/160]` by 9 cells of the computing
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
theorem cell0 : cellOK 141557760 142868480 213647360 219545600 ⟨⟨125961011138, 125961011147⟩, ⟨120450982214, 131572870494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 142868480 144179200 213647360 219545600 ⟨⟨124931364786, 124931364796⟩, ⟨119461062462, 130502367885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 141557760 142868480 219545600 225443840 ⟨⟨129017412001, 129017412009⟩, ⟨123486973306, 134649204086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 142868480 144179200 219545600 225443840 ⟨⟨127967991342, 127967991351⟩, ⟨122477269694, 133558955128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 144179200 145489920 213647360 219545600 ⟨⟨123911534291, 123911534300⟩, ⟨118480423463, 129442235798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 145489920 146800640 213647360 216596480 ⟨⟨122149696190, 122149696198⟩, ⟨117810270807, 126552498434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 145489920 146800640 216596480 219545600 ⟨⟨123652051800, 123652051809⟩, ⟨119303296269, 128064085009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 144179200 145489920 219545600 225443840 ⟨⟨126928467677, 126928467687⟩, ⟨121476932336, 132479152900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 145489920 146800640 219545600 225443840 ⟨⟨125898659534, 125898659543⟩, ⟨120485790660, 131409604588⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 141557760 146800640 213647360 225443840 t = true :=
  ⟨_, (join_su (m := 144179200) (by decide) (join_sr (m := 219545600) (by decide) (join_su (m := 142868480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 142868480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 219545600) (by decide) (join_su (m := 145489920) (by decide) (leaf_ok cell4) (join_sr (m := 216596480) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 145489920) (by decide) (leaf_ok cell7) (leaf_ok cell8))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (27/160 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (163/640 : ℝ) (43/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((213647360 : ℤ) : ℝ) / (D : ℝ)) = (163/640 : ℝ) := by norm_num [D]
  have e3 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

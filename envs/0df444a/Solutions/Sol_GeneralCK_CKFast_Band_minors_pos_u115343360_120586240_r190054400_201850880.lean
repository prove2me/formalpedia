-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_120586240_r190054400_201850880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:34:00.234397+00:00
-- url     : https://prove2.me/submissions/154e04d7-cb4d-475a-9bb3-2dc68a8b1563

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 23/160]`, `ρ ∈ [29/128, 77/320]` by 8 cells of the computing
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
theorem cell0 : cellOK 115343360 116654080 190054400 195952640 ⟨⟨134825777898, 134825777908⟩, ⟨128468585954, 141316392734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 116654080 117964800 190054400 195952640 ⟨⟨133643597374, 133643597382⟩, ⟨127340251600, 140078577695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 115343360 116654080 195952640 201850880 ⟨⟨138391413924, 138391413934⟩, ⟨132013560181, 144901673869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 116654080 117964800 195952640 201850880 ⟨⟨137185963796, 137185963807⟩, ⟨130861841436, 143640741152⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 117964800 119275520 190054400 195952640 ⟨⟨132475671825, 132475671835⟩, ⟨126225291853, 138855935442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 119275520 120586240 190054400 195952640 ⟨⟨131321689617, 131321689625⟩, ⟨125123416949, 137648131405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 117964800 119275520 195952640 201850880 ⟨⟨135994878512, 135994878523⟩, ⟨129723616979, 142395079979⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 119275520 120586240 195952640 201850880 ⟨⟨134817846825, 134817846835⟩, ⟨128598596993, 141164356665⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 120586240 190054400 201850880 t = true :=
  ⟨_, (join_su (m := 117964800) (by decide) (join_sr (m := 195952640) (by decide) (join_su (m := 116654080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 116654080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 195952640) (by decide) (join_su (m := 119275520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 119275520) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (23/160 : ℝ) →
    rho ∈ Set.Icc (29/128 : ℝ) (77/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e2 : (((190054400 : ℤ) : ℝ) / (D : ℝ)) = (29/128 : ℝ) := by norm_num [D]
  have e3 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

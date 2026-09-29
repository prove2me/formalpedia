-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_251658240_r382074880_393216000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:07:12.108664+00:00
-- url     : https://prove2.me/submissions/59033389-5727-41ec-99af-6e30888555cf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 3/10]`, `ρ ∈ [583/1280, 15/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247726080 382074880 384860160 ⟨⟨111521230369, 111521230377⟩, ⟨108215742005, 114863146121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246415360 247726080 384860160 387645440 ⟨⟨112292361850, 112292361856⟩, ⟨108980242676, 115640944189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247726080 249036800 382074880 384860160 ⟨⟨110536608819, 110536608825⟩, ⟨107244441049, 113865035466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247726080 249036800 384860160 387645440 ⟨⟨111301579729, 111301579735⟩, ⟨108002803730, 114636651088⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 246415360 247726080 387645440 390430720 ⟨⟨113063050169, 113063050176⟩, ⟨109744301190, 116418297934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246415360 247726080 390430720 393216000 ⟨⟨113833297574, 113833297582⟩, ⟨110507919781, 117195209610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247726080 249036800 387645440 390430720 ⟨⟨112066118228, 112066118235⟩, ⟨108760734859, 115407833284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247726080 249036800 390430720 393216000 ⟨⟨112830226501, 112830226508⟩, ⟨109518236606, 116178584249⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 250347520 382074880 384860160 ⟨⟨109555533170, 109555533177⟩, ⟨106276589216, 112870568956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249036800 250347520 384860160 387645440 ⟨⟨110314349503, 110314349509⟩, ⟨107028820125, 113636007883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 250347520 251658240 382074880 384860160 ⟨⟨108577958146, 108577958152⟩, ⟨105312142357, 111879700168⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 250347520 251658240 384860160 387645440 ⟨⟨109330625889, 109330625895⟩, ⟨106058247699, 112638968153⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249036800 250347520 387645440 390430720 ⟨⟨111072743984, 111072743991⟩, ⟨107780629897, 114401024090⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 249036800 250347520 390430720 393216000 ⟨⟨111830718735, 111830718743⟩, ⟨108532020641, 115165619706⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 250347520 251658240 387645440 390430720 ⟨⟨110082882150, 110082882157⟩, ⟨106803942134, 113397823931⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250347520 251658240 390430720 393216000 ⟨⟨110834728990, 110834728996⟩, ⟨107549227712, 114156269571⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 251658240 382074880 393216000 t = true :=
  ⟨_, (join_su (m := 249036800) (by decide) (join_sr (m := 387645440) (by decide) (join_su (m := 247726080) (by decide) (join_sr (m := 384860160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 384860160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 247726080) (by decide) (join_sr (m := 390430720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 390430720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 387645440) (by decide) (join_su (m := 250347520) (by decide) (join_sr (m := 384860160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 384860160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 250347520) (by decide) (join_sr (m := 390430720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 390430720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (583/1280 : ℝ) (15/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((382074880 : ℤ) : ℝ) / (D : ℝ)) = (583/1280 : ℝ) := by norm_num [D]
  have e3 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

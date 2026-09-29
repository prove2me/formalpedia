-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_188743680_r794296320_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:26:59.445813+00:00
-- url     : https://prove2.me/submissions/9dca4762-b602-4a9d-8e85-d6bc4eb19e0a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 9/40]`, `ρ ∈ [303/320, 1]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 180879360 794296320 805437440 ⟨⟨321416943799, 321416943810⟩, ⟨309465578519, 333582012816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 180879360 183500800 794296320 805437440 ⟨⟨317382445479, 317382445492⟩, ⟨305528606765, 329450308497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 178257920 180879360 805437440 816578560 ⟨⟨325309353749, 325309353760⟩, ⟨313306761123, 337523509179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 180879360 183500800 805437440 816578560 ⟨⟨321239803192, 321239803203⟩, ⟨309334233608, 333357360211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 183500800 186122240 794296320 805437440 ⟨⟨313368037122, 313368037133⟩, ⟨301611098981, 325339264489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 186122240 188743680 794296320 805437440 ⟨⟨309373300893, 309373300903⟩, ⟨297712644427, 321248457641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 183500800 186122240 805437440 816578560 ⟨⟨317190025831, 317190025842⟩, ⟨305380886406, 329211519599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 186122240 188743680 805437440 816578560 ⟨⟨313159611915, 313159611925⟩, ⟨301446316119, 325085573022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 178257920 180879360 816578560 827719680 ⟨⟨329195461072, 329195461084⟩, ⟨317141763810, 341458552264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 180879360 183500800 816578560 827719680 ⟨⟨325091036315, 325091036326⟩, ⟨313133854068, 337258141138⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 178257920 180879360 827719680 838860800 ⟨⟨333075548252, 333075548265⟩, ⟨320970861940, 345387431247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 180879360 183500800 827719680 838860800 ⟨⟨328936417997, 328936418008⟩, ⟨316927734418, 341152930890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 183500800 186122240 816578560 827719680 ⟨⟨321006065909, 321006065919⟩, ⟨309144838697, 333077684594⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 186122240 188743680 816578560 827719680 ⟨⟨316940148095, 316940148106⟩, ⟨305174321570, 328916777029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 183500800 186122240 827719680 838860800 ⟨⟨324816421365, 324816421376⟩, ⟨312903213229, 336938029721⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 186122240 188743680 827719680 838860800 ⟨⟨320715164504, 320715164515⟩, ⟨308896909456, 332742330744⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 188743680 794296320 838860800 t = true :=
  ⟨_, (join_sr (m := 816578560) (by decide) (join_su (m := 183500800) (by decide) (join_sr (m := 805437440) (by decide) (join_su (m := 180879360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 180879360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 805437440) (by decide) (join_su (m := 186122240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 186122240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 183500800) (by decide) (join_sr (m := 827719680) (by decide) (join_su (m := 180879360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 180879360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 827719680) (by decide) (join_su (m := 186122240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 186122240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (303/320 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((794296320 : ℤ) : ℝ) / (D : ℝ)) = (303/320 : ℝ) := by norm_num [D]
  have e3 : (((838860800 : ℤ) : ℝ) / (D : ℝ)) = (1 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

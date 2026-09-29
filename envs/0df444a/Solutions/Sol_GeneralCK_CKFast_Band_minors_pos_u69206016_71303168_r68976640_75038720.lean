-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u69206016_71303168_r68976640_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:24:17.193035+00:00
-- url     : https://prove2.me/submissions/6afff615-b4e8-4b69-b8a0-08b3e21cde32

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/400, 17/200]`, `ρ ∈ [421/5120, 229/2560]` by 8 cells of the computing
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
theorem cell0 : cellOK 69206016 69730304 68976640 72007680 ⟨⟨82100617514, 82100617524⟩, ⟨78105919484, 86163726742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 69730304 70254592 68976640 72007680 ⟨⟨81647364983, 81647364995⟩, ⟨77676455659, 85685935878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 69206016 69730304 72007680 75038720 ⟨⟨85206717094, 85206717104⟩, ⟨81203460104, 89277757570⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 69730304 70254592 72007680 75038720 ⟨⟨84739832007, 84739832017⟩, ⟨80760333600, 88786377578⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 70254592 70778880 68976640 72007680 ⟨⟨81198746599, 81198746611⟩, ⟨77251330437, 85213087450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 70778880 71303168 68976640 72007680 ⟨⟨80754685062, 80754685072⟩, ⟨76830472102, 84745098285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 70254592 70778880 72007680 75038720 ⟨⟨84277675829, 84277675839⟩, ⟨80321642556, 88300032348⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 70778880 71303168 72007680 75038720 ⟨⟨83820170341, 83820170351⟩, ⟨79887314272, 87818637874⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 69206016 71303168 68976640 75038720 t = true :=
  ⟨_, (join_su (m := 70254592) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 69730304) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 69730304) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 72007680) (by decide) (join_su (m := 70778880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 70778880) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/400 : ℝ) (17/200 : ℝ) →
    rho ∈ Set.Icc (421/5120 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((69206016 : ℤ) : ℝ) / (D : ℝ)) = (33/400 : ℝ) := by norm_num [D]
  have e1 : (((71303168 : ℤ) : ℝ) / (D : ℝ)) = (17/200 : ℝ) := by norm_num [D]
  have e2 : (((68976640 : ℤ) : ℝ) / (D : ℝ)) = (421/5120 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_69206016_r68976640_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:23:30.334599+00:00
-- url     : https://prove2.me/submissions/0779dd92-82bd-486c-a638-97d9d19fab43

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 33/400]`, `ρ ∈ [421/5120, 229/2560]` by 8 cells of the computing
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
theorem cell0 : cellOK 67108864 67633152 68976640 72007680 ⟨⟨83961579059, 83961579069⟩, ⟨79868653591, 88126047904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 67633152 68157440 68976640 72007680 ⟨⟨83488980221, 83488980234⟩, ⟨79421084597, 87627615491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 67108864 67633152 72007680 75038720 ⟨⟨87123175078, 87123175091⟩, ⟨83021833804, 91295375218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 67633152 68157440 72007680 75038720 ⟨⟨86636555328, 86636555338⟩, ⟨82560204538, 90782976008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 68157440 68681728 68976640 72007680 ⟨⟨83021343235, 83021343246⟩, ⟨78978158019, 87134478371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 68681728 69206016 68976640 72007680 ⟨⟨82558583282, 82558583294⟩, ⟨78539795251, 86646545192⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 68157440 68681728 72007680 75038720 ⟨⟨86154995923, 86154995933⟩, ⟨82103318620, 90275967772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 68681728 69206016 72007680 75038720 ⟨⟨85678411107, 85678411117⟩, ⟨81651096423, 89774258306⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 69206016 68976640 75038720 t = true :=
  ⟨_, (join_su (m := 68157440) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 67633152) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 67633152) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 72007680) (by decide) (join_su (m := 68681728) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 68681728) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (33/400 : ℝ) →
    rho ∈ Set.Icc (421/5120 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((69206016 : ℤ) : ℝ) / (D : ℝ)) = (33/400 : ℝ) := by norm_num [D]
  have e2 : (((68976640 : ℤ) : ℝ) / (D : ℝ)) = (421/5120 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

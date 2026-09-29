-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u65011712_67108864_r68976640_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:05:22.135111+00:00
-- url     : https://prove2.me/submissions/8eec6d83-b788-4f5a-8945-25a59fe3d134

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/400, 2/25]`, `ρ ∈ [421/5120, 229/2560]` by 8 cells of the computing
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
theorem cell0 : cellOK 65011712 65536000 68976640 72007680 ⟨⟨85903361256, 85903361266⟩, ⟨81706992116, 90174635815⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 65536000 66060288 68976640 72007680 ⟨⟨85410025500, 85410025513⟩, ⟨81240029359, 89654063762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 65011712 65536000 72007680 75038720 ⟨⟨89122044928, 89122044939⟩, ⟨84917443756, 93400803882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 65536000 66060288 72007680 75038720 ⟨⟨88614284751, 88614284762⟩, ⟨84436006480, 92865873924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 66060288 66584576 68976640 72007680 ⟨⟨84922011703, 84922011713⟩, ⟨80778042605, 89139175062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 66584576 67108864 68976640 72007680 ⟨⟨84439226577, 84439226590⟩, ⟨80320945462, 88629869162⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 66060288 66584576 72007680 75038720 ⟨⟨88111948841, 88111948852⟩, ⟨83959650355, 92336726356⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 66584576 67108864 72007680 75038720 ⟨⟨87614942960, 87614942970⟩, ⟨83488287933, 91813259784⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 65011712 67108864 68976640 75038720 t = true :=
  ⟨_, (join_su (m := 66060288) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 65536000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 65536000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 72007680) (by decide) (join_su (m := 66584576) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 66584576) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/400 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (421/5120 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((65011712 : ℤ) : ℝ) / (D : ℝ)) = (31/400 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((68976640 : ℤ) : ℝ) / (D : ℝ)) = (421/5120 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

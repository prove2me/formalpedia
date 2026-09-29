-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u73400320_75497472_r68976640_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:29:10.48488+00:00
-- url     : https://prove2.me/submissions/236b432d-757c-4612-a73e-3e67e6ed7d6b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/80, 9/100]`, `ρ ∈ [421/5120, 229/2560]` by 12 cells of the computing
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
theorem cell0 : cellOK 73400320 73924608 68976640 70492160 ⟨⟨77846103256, 77846103266⟩, ⟨75043725077, 80682652420⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 73400320 73924608 70492160 72007680 ⟨⟨79352524524, 79352524536⟩, ⟨76546395972, 82192696883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 73924608 74448896 68976640 70492160 ⟨⟨77431129015, 77431129024⟩, ⟨74643968462, 80252116361⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 73924608 74448896 70492160 72007680 ⟨⟨78931020335, 78931020344⟩, ⟨76140107170, 81755635823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 73400320 73924608 72007680 75038720 ⟨⟨81599785645, 81599785654⟩, ⟨77778680399, 85483116005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 73924608 74448896 72007680 75038720 ⟨⟨81168636520, 81168636529⟩, ⟨77369089378, 85029764251⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 74448896 74973184 68976640 70492160 ⟨⟨77020194096, 77020194105⟩, ⟨74248069102, 79825807268⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 74448896 74973184 70492160 72007680 ⟨⟨78513600470, 78513600482⟩, ⟨75737721128, 81322846160⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 74973184 75497472 68976640 70492160 ⟨⟨76613234100, 76613234109⟩, ⟨73855965879, 79403657328⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 74973184 75497472 70492160 72007680 ⟨⟨78100200077, 78100200086⟩, ⟨75339176268, 80894259639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 74448896 74973184 72007680 75038720 ⟨⟨80741636975, 80741636984⟩, ⟨76963395028, 84580825353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 74973184 75497472 72007680 75038720 ⟨⟨80318721517, 80318721527⟩, ⟨76561536371, 84136229064⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 73400320 75497472 68976640 75038720 t = true :=
  ⟨_, (join_su (m := 74448896) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 73924608) (by decide) (join_sr (m := 70492160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 70492160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 73924608) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 72007680) (by decide) (join_su (m := 74973184) (by decide) (join_sr (m := 70492160) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 70492160) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 74973184) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/80 : ℝ) (9/100 : ℝ) →
    rho ∈ Set.Icc (421/5120 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((73400320 : ℤ) : ℝ) / (D : ℝ)) = (7/80 : ℝ) := by norm_num [D]
  have e1 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e2 : (((68976640 : ℤ) : ℝ) / (D : ℝ)) = (421/5120 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

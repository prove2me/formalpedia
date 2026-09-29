-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_35651584_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:34:53.251851+00:00
-- url     : https://prove2.me/submissions/e20f974b-c2ba-432a-85ed-1ceedab9d41a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 17/400]`, `ρ ∈ [3/40, 229/2560]` by 12 cells of the computing
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
theorem cell0 : cellOK 33554432 34078720 62914560 65945600 ⟨⟨122087849184, 122087849199⟩, ⟨115212861081, 129152224177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 34078720 34603008 62914560 65945600 ⟨⟨120994731064, 120994731084⟩, ⟨114194957020, 127980213155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 33554432 34078720 65945600 68976640 ⟨⟨126546864531, 126546864551⟩, ⟨119678931717, 133600240888⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 34078720 34603008 65945600 68976640 ⟨⟨125429572981, 125429572997⟩, ⟨118636046445, 132404996468⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 34603008 35127296 62914560 65945600 ⟨⟨119921844063, 119921844079⟩, ⟨113195579552, 126830248006⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 35127296 35651584 62914560 65945600 ⟨⟨118868595406, 118868595426⟩, ⟨112214193460, 125701673996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 34603008 35127296 65945600 68976640 ⟨⟨124332655147, 124332655167⟩, ⟨117611868966, 131231896314⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 35127296 35651584 65945600 68976640 ⟨⟨123255522073, 123255522092⟩, ⟨116605865864, 130080291772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 33554432 34603008 68976640 72007680 ⟨⟨130352625254, 130352625274⟩, ⟨120558505786, 140527839103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 33554432 34603008 72007680 75038720 ⟨⟨134642681293, 134642681309⟩, ⟨124855656662, 144803460254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 34603008 35651584 68976640 72007680 ⟨⟨128113204551, 128113204571⟩, ⟨118521451113, 138072181507⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 34603008 35651584 72007680 75038720 ⟨⟨132360288306, 132360288321⟩, ⟨122773563663, 142307370431⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 35651584 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 34603008) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 34078720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 34078720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 65945600) (by decide) (join_su (m := 35127296) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 35127296) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 34603008) (by decide) (join_sr (m := 72007680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 72007680) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (17/400 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((35651584 : ℤ) : ℝ) / (D : ℝ)) = (17/400 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

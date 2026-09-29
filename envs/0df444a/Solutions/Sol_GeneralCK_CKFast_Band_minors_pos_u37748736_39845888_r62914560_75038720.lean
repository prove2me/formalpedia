-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u37748736_39845888_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:36:15.119104+00:00
-- url     : https://prove2.me/submissions/18420445-898d-4e95-99f0-a78f8e487046

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/200, 19/400]`, `ρ ∈ [3/40, 229/2560]` by 14 cells of the computing
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
theorem cell0 : cellOK 37748736 38273024 62914560 65945600 ⟨⟨113877764313, 113877764328⟩, ⟨107559813068, 120358525230⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 38273024 38797312 62914560 65945600 ⟨⟨112931137223, 112931137242⟩, ⟨106676241237, 119345933497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 37748736 38273024 65945600 68976640 ⟨⟨118147569148, 118147569167⟩, ⟨111831187539, 124623732819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 38273024 38797312 65945600 68976640 ⟨⟨117177993598, 117177993616⟩, ⟨110924118376, 123588836004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 38797312 39321600 62914560 65945600 ⟨⟨112000596922, 112000596937⟩, ⟨105807447714, 118350817366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 39321600 39845888 62914560 65945600 ⟨⟨111085709600, 111085709618⟩, ⟨104953039252, 117372699486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 38797312 39321600 65945600 68976640 ⟨⟨116224667315, 116224667334⟩, ⟨110032015517, 122571548040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 39321600 39845888 65945600 68976640 ⟨⟨115287157626, 115287157640⟩, ⟨109154485601, 121571394112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 37748736 38273024 68976640 72007680 ⟨⟨122346744291, 122346744310⟩, ⟨116032963907, 128817349386⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 38273024 38797312 68976640 72007680 ⟨⟨121355352308, 121355352323⟩, ⟨115103516823, 127761288783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 37748736 38797312 72007680 75038720 ⟨⟨125969573882, 125969573897⟩, ⟨116934435607, 135329130517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 38797312 39321600 68976640 72007680 ⟨⟨120380348856, 120380348875⟩, ⟨114189200710, 126722947349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 39321600 39845888 68976640 72007680 ⟨⟨119421302945, 119421302959⟩, ⟨113289622671, 125701853337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 38797312 39845888 72007680 75038720 ⟨⟨123978201531, 123978201534⟩, ⟨115112143695, 133157948051⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 37748736 39845888 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 38797312) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 38273024) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 38273024) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 65945600) (by decide) (join_su (m := 39321600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 39321600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 38797312) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 38273024) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 72007680) (by decide) (join_su (m := 39321600) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/200 : ℝ) (19/400 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((37748736 : ℤ) : ℝ) / (D : ℝ)) = (9/200 : ℝ) := by norm_num [D]
  have e1 : (((39845888 : ℤ) : ℝ) / (D : ℝ)) = (19/400 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

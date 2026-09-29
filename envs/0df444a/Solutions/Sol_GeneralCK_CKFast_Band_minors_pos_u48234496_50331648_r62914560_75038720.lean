-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u48234496_50331648_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:42:24.783354+00:00
-- url     : https://prove2.me/submissions/106e628a-da89-4a7e-9482-c88d4c05980b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/400, 3/50]`, `ρ ∈ [3/40, 229/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 48234496 48758784 62914560 65945600 ⟨⟨97574024600, 97574024613⟩, ⟨92307918909, 102957185855⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 48758784 49283072 62914560 65945600 ⟨⟨96881779213, 96881779228⟩, ⟨91658718613, 102220153288⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 48234496 48758784 65945600 68976640 ⟨⟨101416151817, 101416151833⟩, ⟨96144344915, 106803332763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 48758784 49283072 65945600 68976640 ⟨⟨100704233304, 100704233316⟩, ⟨95475258031, 106046885577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 49283072 49807360 62914560 65945600 ⟨⟨96199285468, 96199285480⟩, ⟨91018533747, 101493648740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 49807360 50331648 62914560 65945600 ⟨⟨95526323778, 95526323794⟩, ⟨90387163695, 100777432416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 49283072 49807360 65945600 68976640 ⟨⟨100002223783, 100002223799⟩, ⟨94815353888, 105301112302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 49807360 50331648 65945600 68976640 ⟨⟨99309902567, 99309902579⟩, ⟨94164430330, 104565772532⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 48234496 48758784 68976640 72007680 ⟨⟨105206455156, 105206455169⟩, ⟨99929726831, 110596903884⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 48758784 49283072 68976640 72007680 ⟨⟨104475623325, 104475623340⟩, ⟨99241501493, 109821812376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 48234496 48758784 72007680 75038720 ⟨⟨108946426649, 108946426662⟩, ⟨103665512308, 114339435344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 48758784 49283072 72007680 75038720 ⟨⟨108197406895, 108197406908⟩, ⟨102958863409, 113546434240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 49283072 49807360 68976640 72007680 ⟨⟨103754843529, 103754843541⟩, ⟨98562612025, 109057526282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 49807360 50331648 68976640 72007680 ⟨⟨103043894287, 103043894303⟩, ⟨97892855064, 108303804890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 49283072 49807360 72007680 75038720 ⟨⟨107458568848, 107458568861⟩, ⟨102261690258, 112764356632⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 49807360 50331648 72007680 75038720 ⟨⟨106729690560, 106729690572⟩, ⟨101573788575, 111992961822⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 48234496 50331648 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 49283072) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 48758784) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 48758784) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 65945600) (by decide) (join_su (m := 49807360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 49807360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 49283072) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 48758784) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 48758784) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 72007680) (by decide) (join_su (m := 49807360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 49807360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/400 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((48234496 : ℤ) : ℝ) / (D : ℝ)) = (23/400 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

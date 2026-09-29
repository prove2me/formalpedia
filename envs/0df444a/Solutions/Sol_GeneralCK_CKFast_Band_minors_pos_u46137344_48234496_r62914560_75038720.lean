-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u46137344_48234496_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:42:07.6176+00:00
-- url     : https://prove2.me/submissions/35a6e30f-ac57-4f26-9037-4514b443b5aa

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/200, 23/400]`, `ρ ∈ [3/40, 229/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 46137344 46661632 62914560 65945600 ⟨⟨100445163829, 100445163845⟩, ⟨94999112478, 106015667636⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 46661632 47185920 62914560 65945600 ⟨⟨99711572521, 99711572534⟩, ⟨94311714524, 105233966648⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 46137344 46661632 65945600 68976640 ⟨⟨104367577941, 104367577958⟩, ⟨98916788198, 109940942055⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 46661632 47185920 65945600 68976640 ⟨⟨103613673794, 103613673807⟩, ⟨98208819351, 109139238023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 47185920 47710208 62914560 65945600 ⟨⟨98988683693, 98988683705⟩, ⟨93634200002, 104463832900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 47710208 48234496 62914560 65945600 ⟨⟨98276248161, 98276248177⟩, ⟨92966341548, 103704993905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 47185920 47710208 65945600 68976640 ⟨⟨102870633496, 102870633512⟩, ⟨97510907216, 108349248904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 47710208 48234496 65945600 68976640 ⟨⟨102138206944, 102138206957⟩, ⟨96822822986, 107570701892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 46137344 46661632 68976640 72007680 ⟨⟨108234978719, 108234978732⟩, ⟨102780278395, 113810408601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 46661632 47185920 68976640 72007680 ⟨⟨107461582344, 107461582360⟩, ⟨102052547077, 112989532880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 46137344 46661632 72007680 75038720 ⟨⟨112049006179, 112049006192⟩, ⟨106591173578, 117625756381⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 46661632 47185920 72007680 75038720 ⟨⟨111256899590, 111256899602⟩, ⟨105844450944, 116786500417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 47185920 47710208 68976640 72007680 ⟨⟨106699195451, 106699195463⟩, ⟨101335030131, 112180503952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 47710208 48234496 68976640 72007680 ⟨⟨105947567363, 105947567379⟩, ⟨100627497669, 111383049046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 47185920 47710208 72007680 75038720 ⟨⟨110475933453, 110475933466⟩, ⟨105108085775, 115959208466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 47710208 48234496 72007680 75038720 ⟨⟨109705856883, 109705856896⟩, ⟨104381847443, 115143608112⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 46137344 48234496 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 47185920) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 46661632) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 46661632) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 65945600) (by decide) (join_su (m := 47710208) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 47710208) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 47185920) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 46661632) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 46661632) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 72007680) (by decide) (join_su (m := 47710208) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 47710208) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/200 : ℝ) (23/400 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((46137344 : ℤ) : ℝ) / (D : ℝ)) = (11/200 : ℝ) := by norm_num [D]
  have e1 : (((48234496 : ℤ) : ℝ) / (D : ℝ)) = (23/400 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

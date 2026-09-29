-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u39845888_41943040_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:37:16.786332+00:00
-- url     : https://prove2.me/submissions/66f173ae-143b-4778-a6ac-0da55a341ec2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/400, 1/20]`, `ρ ∈ [3/40, 229/2560]` by 14 cells of the computing
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
theorem cell0 : cellOK 39845888 40370176 62914560 65945600 ⟨⟨110186057299, 110186057317⟩, ⟨104112636809, 116411120150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 40370176 40894464 62914560 65945600 ⟨⟨109301237181, 109301237195⟩, ⟨103285874880, 115465636461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 39845888 40370176 65945600 68976640 ⟨⟨114365047456, 114365047474⟩, ⟨108291149306, 120587916756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 40370176 40894464 65945600 68976640 ⟨⟨113457934663, 113457934677⟩, ⟨107441640704, 119620675032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 40894464 41418752 62914560 65945600 ⟨⟨108430860821, 108430860839⟩, ⟨102472400902, 114535821556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 41418752 41943040 62914560 65945600 ⟨⟨107574553589, 107574553603⟩, ⟨101671874659, 113621263910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 40894464 41418752 65945600 68976640 ⟨⟨112565431319, 112565431336⟩, ⟨106605606680, 118669243784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 41418752 41943040 65945600 68976640 ⟨⟨111687163113, 111687163127⟩, ⟨105782706347, 117733212936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 39845888 40370176 68976640 72007680 ⟨⟨118477798945, 118477798963⟩, ⟨112404403682, 124697552035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 40370176 40894464 68976640 72007680 ⟨⟨117549435935, 117549435949⟩, ⟨111533177942, 123709604963⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 39845888 40894464 72007680 75038720 ⟨⟨122050319986, 122050320000⟩, ⟨113346681862, 131057469599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 40894464 41418752 68976640 72007680 ⟨⟨116635827005, 116635827023⟩, ⟨110675592337, 122737589153⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 41418752 41943040 68976640 72007680 ⟨⟨115736598676, 115736598690⟩, ⟨109831305824, 121781096467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 40894464 41943040 72007680 75038720 ⟨⟨120182733420, 120182733435⟩, ⟨111635241495, 129024074180⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 39845888 41943040 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 40894464) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 40370176) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 40370176) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 65945600) (by decide) (join_su (m := 41418752) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 41418752) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 40894464) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 40370176) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 72007680) (by decide) (join_su (m := 41418752) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/400 : ℝ) (1/20 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((39845888 : ℤ) : ℝ) / (D : ℝ)) = (19/400 : ℝ) := by norm_num [D]
  have e1 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

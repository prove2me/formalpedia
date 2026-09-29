-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u65011712_67108864_r62914560_68976640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:05:04.043085+00:00
-- url     : https://prove2.me/submissions/01176d6b-87e7-4e5f-9749-4d56602c4422

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/400, 2/25]`, `ρ ∈ [3/40, 421/5120]` by 13 cells of the computing
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
theorem cell0 : cellOK 65011712 65536000 62914560 64430080 ⟨⟨78541397697, 78541397708⟩, ⟨75483080271, 81640998641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 65011712 65536000 64430080 65945600 ⟨⟨80192040532, 80192040542⟩, ⟨77129756058, 83295424289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 65536000 66060288 62914560 64430080 ⟨⟨78082059648, 78082059661⟩, ⟨75042439698, 81162493103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 65536000 66060288 64430080 65945600 ⟨⟨79724956792, 79724956805⟩, ⟨76681361206, 82809185887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 65011712 65536000 65945600 68976640 ⟨⟨82652188252, 82652188264⟩, ⟨78464508621, 86915528387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 65536000 66060288 65945600 68976640 ⟨⟨82173692646, 82173692657⟩, ⟨78012429340, 86409736446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 66060288 66584576 62914560 64430080 ⟨⟨77627788386, 77627788396⟩, ⟨74606614331, 80689314491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 66060288 66584576 64430080 65945600 ⟨⟨79262999677, 79262999687⟩, ⟨76237842263, 82328333266⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 66584576 67108864 62914560 64430080 ⟨⟨77178493292, 77178493304⟩, ⟨74175518669, 80221366859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 66584576 67108864 64430080 65945600 ⟨⟨78806077908, 78806077921⟩, ⟨75799113031, 81852769865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 66060288 66584576 65945600 68976640 ⟨⟨81700410001, 81700410014⟩, ⟨77565214333, 85909522046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 66584576 67108864 65945600 67461120 ⟨⟨80425537199, 80425537209⟩, ⟨77414665936, 83475964258⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 66584576 67108864 67461120 68976640 ⟨⟨82036961508, 82036961518⟩, ⟨79022266088, 85091042037⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 65011712 67108864 62914560 68976640 t = true :=
  ⟨_, (join_su (m := 66060288) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 65536000) (by decide) (join_sr (m := 64430080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 64430080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 65536000) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 65945600) (by decide) (join_su (m := 66584576) (by decide) (join_sr (m := 64430080) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 64430080) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 66584576) (by decide) (leaf_ok cell10) (join_sr (m := 67461120) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/400 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (421/5120 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((65011712 : ℤ) : ℝ) / (D : ℝ)) = (31/400 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((68976640 : ℤ) : ℝ) / (D : ℝ)) = (421/5120 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

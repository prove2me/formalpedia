-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_249036800_r214958080_220528640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:51:56.111653+00:00
-- url     : https://prove2.me/submissions/24ebcb05-0b05-4530-8af1-9bc43f8e872f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 19/64]`, `ρ ∈ [41/160, 673/2560]` by 15 cells of the computing
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
theorem cell0 : cellOK 246415360 247070720 214958080 216350720 ⟨⟨64300660153, 64300660159⟩, ⟨62843091526, 65766737650⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246415360 247070720 216350720 217743360 ⟨⟨64702733238, 64702733245⟩, ⟨63243481972, 66170498983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247070720 247726080 214958080 216350720 ⟨⟨64004468820, 64004468822⟩, ⟨62549842300, 65467578675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247070720 247726080 216350720 217743360 ⟨⟨64404803841, 64404803845⟩, ⟨62948498756, 65869597902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 246415360 247070720 217743360 220528640 ⟨⟨65305562764, 65305562771⟩, ⟨63608153123, 67014930769⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 247070720 247726080 217743360 219136000 ⟨⟨64804991343, 64804991347⟩, ⟨63347007892, 66271469396⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247070720 247726080 219136000 220528640 ⟨⟨65205031664, 65205031668⟩, ⟨63745370051, 66673193499⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247726080 248381440 214958080 216350720 ⟨⟨63708976437, 63708976442⟩, ⟨62257278911, 65169131922⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 247726080 248381440 216350720 217743360 ⟨⟨64107576026, 64107576032⟩, ⟨62654204005, 65569411673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 248381440 249036800 214958080 216350720 ⟨⟨63414178040, 63414178046⟩, ⟨61965396482, 64871392332⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 248381440 249036800 216350720 217743360 ⟨⟨63811044815, 63811044821⟩, ⟨62360592829, 65269935226⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 247726080 248381440 217743360 219136000 ⟨⟨64506030001, 64506030006⟩, ⟨63050983674, 65969545610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 247726080 248381440 219136000 220528640 ⟨⟨64904338695, 64904338701⟩, ⟨63447618252, 66369534066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 248381440 249036800 217743360 219136000 ⟨⟨64207767860, 64207767866⟩, ⟨62755645626, 65668334202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 248381440 249036800 219136000 220528640 ⟨⟨64604347505, 64604347510⟩, ⟨63150555202, 66066589591⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 249036800 214958080 220528640 t = true :=
  ⟨_, (join_su (m := 247726080) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 247070720) (by decide) (join_sr (m := 216350720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 216350720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 247070720) (by decide) (leaf_ok cell4) (join_sr (m := 219136000) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 217743360) (by decide) (join_su (m := 248381440) (by decide) (join_sr (m := 216350720) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 216350720) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 248381440) (by decide) (join_sr (m := 219136000) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 219136000) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (673/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((220528640 : ℤ) : ℝ) / (D : ℝ)) = (673/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

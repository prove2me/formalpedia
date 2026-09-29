-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u180879360_183500800_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:26:29.905971+00:00
-- url     : https://prove2.me/submissions/7359a479-3a63-42e4-97d4-a7f9cd5681c8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [69/320, 7/32]`, `ρ ∈ [87/512, 113/640]` by 8 cells of the computing
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
theorem cell0 : cellOK 180879360 181534720 142540800 145326080 ⟨⟨67350200682, 67350200688⟩, ⟨65249410020, 69469265321⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 181534720 182190080 142540800 145326080 ⟨⟨67064911638, 67064911643⟩, ⟨64970591756, 69177411281⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 180879360 181534720 145326080 148111360 ⟨⟨68586668685, 68586668691⟩, ⟨66480958445, 70710644632⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 181534720 182190080 145326080 148111360 ⟨⟨68296644482, 68296644486⟩, ⟨66197418274, 70414042584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 182190080 182845440 142540800 145326080 ⟨⟨66780810273, 66780810279⟩, ⟨64692922686, 68886784189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 182845440 183500800 142540800 145326080 ⟨⟨66497886286, 66497886294⟩, ⟨64416392867, 68597373370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 182190080 182845440 145326080 148111360 ⟨⟨68007822084, 68007822090⟩, ⟨65915041429, 70118681600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 182845440 183500800 145326080 148111360 ⟨⟨67720191103, 67720191109⟩, ⟨65633817879, 69824550913⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 180879360 183500800 142540800 148111360 t = true :=
  ⟨_, (join_su (m := 182190080) (by decide) (join_sr (m := 145326080) (by decide) (join_su (m := 181534720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 181534720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 145326080) (by decide) (join_su (m := 182845440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 182845440) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (69/320 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((180879360 : ℤ) : ℝ) / (D : ℝ)) = (69/320 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

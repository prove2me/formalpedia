-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u62914560_67108864_r123535360_135659520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:12:55.177446+00:00
-- url     : https://prove2.me/submissions/21d42986-9372-4202-b612-fdb39e2f973f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/40, 2/25]`, `ρ ∈ [377/2560, 207/1280]` by 13 cells of the computing
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
theorem cell0 : cellOK 62914560 63963136 123535360 126566400 ⟨⟨141996825830, 141996825842⟩, ⟨135578360345, 148557599318⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 62914560 63963136 126566400 129597440 ⟨⟨144766840657, 144766840668⟩, ⟨138342759447, 151331910663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 63963136 65011712 123535360 126566400 ⟨⟨140554763884, 140554763895⟩, ⟨134208636257, 147040494433⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 63963136 65011712 126566400 129597440 ⟨⟨143306826766, 143306826780⟩, ⟨136954752064, 149797236957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 62914560 63963136 129597440 135659520 ⟨⟨148879493253, 148879493267⟩, ⟨140175010090, 157836566584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 63963136 65011712 129597440 135659520 ⟨⟨147393413928, 147393413940⟩, ⟨138789134280, 156245434059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 65011712 66060288 123535360 126566400 ⟨⟨139139340777, 139139340783⟩, ⟨132863838737, 145551822321⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 65011712 66060288 126566400 129597440 ⟨⟨141873549469, 141873549474⟩, ⟨135591788745, 148291071669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 66060288 67108864 123535360 126566400 ⟨⟨137749746623, 137749746637⟩, ⟨131543218224, 144090709482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 66060288 67108864 126566400 129597440 ⟨⟨140466201920, 140466201931⟩, ⟨134253121849, 146812545589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 65011712 66060288 129597440 135659520 ⟨⟨145934198006, 145934198011⟩, ⟨137427826986, 154683602695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 66060288 67108864 129597440 132628480 ⟨⟨143161341652, 143161341666⟩, ⟨136942021261, 149512765701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 66060288 67108864 132628480 135659520 ⟨⟨145835566171, 145835566182⟩, ⟨139610305827, 152191781087⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 62914560 67108864 123535360 135659520 t = true :=
  ⟨_, (join_su (m := 65011712) (by decide) (join_sr (m := 129597440) (by decide) (join_su (m := 63963136) (by decide) (join_sr (m := 126566400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 126566400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 63963136) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 129597440) (by decide) (join_su (m := 66060288) (by decide) (join_sr (m := 126566400) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 126566400) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 66060288) (by decide) (leaf_ok cell10) (join_sr (m := 132628480) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/40 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (377/2560 : ℝ) (207/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((123535360 : ℤ) : ℝ) / (D : ℝ)) = (377/2560 : ℝ) := by norm_num [D]
  have e3 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

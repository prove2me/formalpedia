-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u20971520_25165824_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:17:35.867168+00:00
-- url     : https://prove2.me/submissions/d5e291b9-901a-4311-b267-cc9c7f45cce9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/40, 3/100]`, `ρ ∈ [3/40, 229/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 20971520 22020096 62914560 65945600 ⟨⟨155580727742, 155580727768⟩, ⟨142266197452, 169575652185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 20971520 22020096 65945600 68976640 ⟨⟨160627451983, 160627452004⟩, ⟨147367640824, 174547759933⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 22020096 23068672 62914560 65945600 ⟨⟨151975355194, 151975355214⟩, ⟨139053608128, 165543022975⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 22020096 23068672 65945600 68976640 ⟨⟨156973102874, 156973102894⟩, ⟨144098827068, 170475105973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 20971520 22020096 68976640 72007680 ⟨⟨165552296787, 165552296808⟩, ⟨152348720450, 179397271324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 20971520 22020096 72007680 75038720 ⟨⟨170361287958, 170361287985⟩, ⟨157215205371, 184130430031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 22020096 23068672 68976640 72007680 ⟨⟨161853320577, 161853320598⟩, ⟨149028133971, 175288740881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 22020096 23068672 72007680 75038720 ⟨⟨166621670390, 166621670411⟩, ⟨153846945116, 179989803301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 23068672 24117248 62914560 65945600 ⟨⟨148545714219, 148545714239⟩, ⟨135993017608, 161712519759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 23068672 24117248 65945600 68976640 ⟨⟨153493665660, 153493665681⟩, ⟨140981986932, 166602780007⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 24117248 25165824 62914560 65945600 ⟨⟨145278479137, 145278479156⟩, ⟨133073192497, 158068454558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 24117248 25165824 65945600 68976640 ⟨⟨150176085870, 150176085890⟩, ⟨138006059168, 162915488214⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 23068672 24117248 68976640 72007680 ⟨⟨158328268344, 158328268364⟩, ⟨145859298630, 171378615223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 23068672 24117248 72007680 75038720 ⟨⟨163054846010, 163054846030⟩, ⟨150630041952, 176045556780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 24117248 25165824 68976640 72007680 ⟨⟨154964358789, 154964358808⟩, ⟨142831332788, 167651988929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 24117248 25165824 72007680 75038720 ⟨⟨159648306852, 159648306871⟩, ⟨147553799224, 172283166362⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 20971520 25165824 62914560 75038720 t = true :=
  ⟨_, (join_su (m := 23068672) (by decide) (join_sr (m := 68976640) (by decide) (join_su (m := 22020096) (by decide) (join_sr (m := 65945600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 65945600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 22020096) (by decide) (join_sr (m := 72007680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 72007680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 68976640) (by decide) (join_su (m := 24117248) (by decide) (join_sr (m := 65945600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 65945600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 24117248) (by decide) (join_sr (m := 72007680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 72007680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/40 : ℝ) (3/100 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((20971520 : ℤ) : ℝ) / (D : ℝ)) = (1/40 : ℝ) := by norm_num [D]
  have e1 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

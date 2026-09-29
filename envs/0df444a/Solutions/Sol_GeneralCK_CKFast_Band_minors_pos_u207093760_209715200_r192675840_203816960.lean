-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u207093760_209715200_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:18:38.834824+00:00
-- url     : https://prove2.me/submissions/f312c961-f4f9-42a0-8f72-53c523829f15

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [79/320, 1/4]`, `ρ ∈ [147/640, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 207093760 207749120 192675840 195461120 ⟨⟨75592436961, 75592436968⟩, ⟨73645833559, 77554128261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 207749120 208404480 192675840 195461120 ⟨⟨75273826754, 75273826757⟩, ⟨73332608187, 77230068323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 207093760 207749120 195461120 198246400 ⟨⟨76625338998, 76625339005⟩, ⟨74674485293, 78591282545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 207749120 208404480 195461120 198246400 ⟨⟨76302775294, 76302775297⟩, ⟨74357316740, 78263259024⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 208404480 209059840 192675840 195461120 ⟨⟨74956239078, 74956239083⟩, ⟨73020378367, 76907058351⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209059840 209715200 192675840 195461120 ⟨⟨74639666134, 74639666141⟩, ⟨72709136510, 76585090319⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 208404480 209059840 195461120 198246400 ⟨⟨75981242251, 75981242259⟩, ⟨74041151881, 77936293585⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 209059840 209715200 195461120 198246400 ⟨⟨75660732032, 75660732039⟩, ⟨73725983087, 77610378159⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 207093760 207749120 198246400 201031680 ⟨⟨77656959223, 77656959229⟩, ⟨75701862658, 79627147478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 207749120 208404480 198246400 201031680 ⟨⟨77330456600, 77330456603⟩, ⟨75380765368, 79295175088⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 207093760 207749120 201031680 203816960 ⟨⟨78687304767, 78687304773⟩, ⟨76727972735, 80661730243⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 207749120 208404480 201031680 203816960 ⟨⟨78356877699, 78356877702⟩, ⟨76402961049, 80325823588⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 208404480 209059840 198246400 201031680 ⟨⟨77004992631, 77004992637⟩, ⟨75060679777, 78964268751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 209059840 209715200 198246400 201031680 ⟨⟨76680559433, 76680559439⟩, ⟨74741598214, 78634420362⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 208404480 209059840 201031680 203816960 ⟨⟨78027497135, 78027497142⟩, ⟨76078968930, 79990990819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 209059840 209715200 201031680 203816960 ⟨⟨77699155155, 77699155161⟩, ⟨75755988664, 79657223790⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 207093760 209715200 192675840 203816960 t = true :=
  ⟨_, (join_sr (m := 198246400) (by decide) (join_su (m := 208404480) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 207749120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 207749120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 195461120) (by decide) (join_su (m := 209059840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 209059840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 208404480) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 207749120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 207749120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 201031680) (by decide) (join_su (m := 209059840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 209059840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (79/320 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((207093760 : ℤ) : ℝ) / (D : ℝ)) = (79/320 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_209715200_r226099200_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:28:25.827784+00:00
-- url     : https://prove2.me/submissions/c03fe652-2fb4-476b-83e8-c81c8aaa66ff

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 1/4]`, `ρ ∈ [69/256, 181/640]` by 19 cells of the computing
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
theorem cell0 : cellOK 204472320 205783040 226099200 228884480 ⟨⟨89190977041, 89190977047⟩, ⟨85816743692, 92607306347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 204472320 205783040 228884480 231669760 ⟨⟨90222260107, 90222260115⟩, ⟨86840327672, 93646307778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 205783040 207093760 226099200 228884480 ⟨⟨88453982332, 88453982336⟩, ⟨85095764635, 91853996398⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205783040 207093760 228884480 231669760 ⟨⟨89477655167, 89477655172⟩, ⟨86111767880, 92885359282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 204472320 205783040 231669760 234455040 ⟨⟨91252296656, 91252296662⟩, ⟨87862675824, 94684051685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 204472320 205783040 234455040 237240320 ⟨⟨92281093713, 92281093719⟩, ⟨88883795111, 95720545164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 205783040 207093760 231669760 234455040 ⟨⟨90500108972, 90500108974⟩, ⟨87126562388, 93915492533⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 205783040 207093760 234455040 237240320 ⟨⟨91521350572, 91521350577⟩, ⟨88140154926, 94944403043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 207093760 207749120 226099200 228884480 ⟨⟨87904211596, 87904211603⟩, ⟨85907085332, 89916442801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 207749120 208404480 226099200 228884480 ⟨⟨87539098806, 87539098809⟩, ⟨85547472606, 89545767858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 207093760 208404480 228884480 231669760 ⟨⟨88737604814, 88737604821⟩, ⟨85387598576, 92129133401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 208404480 209059840 226099200 228884480 ⟨⟨87175097140, 87175097146⟩, ⟨85188944270, 89176231184⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 209059840 209715200 226099200 228884480 ⟨⟨86812198372, 86812198380⟩, ⟨84831492300, 88807824340⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 208404480 209059840 228884480 231669760 ⟨⟨88185515505, 88185515512⟩, ⟨86195216142, 90190797323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 209059840 209715200 228884480 231669760 ⟨⟨87818844438, 87818844446⟩, ⟨85834000719, 89818609567⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 207093760 208404480 231669760 234455040 ⟨⟨89752501786, 89752501792⟩, ⟨86394865539, 93151681688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 207093760 208404480 234455040 237240320 ⟨⟨90766213342, 90766213348⟩, ⟨87400956932, 94173034408⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 208404480 209715200 231669760 234455040 ⟨⟨89009407645, 89009407651⟩, ⟨85667520338, 92392549100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 208404480 209715200 234455040 237240320 ⟨⟨90015614355, 90015614362⟩, ⟨86666135974, 93406369017⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 209715200 226099200 237240320 t = true :=
  ⟨_, (join_su (m := 207093760) (by decide) (join_sr (m := 231669760) (by decide) (join_su (m := 205783040) (by decide) (join_sr (m := 228884480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 228884480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 205783040) (by decide) (join_sr (m := 234455040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 234455040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 231669760) (by decide) (join_su (m := 208404480) (by decide) (join_sr (m := 228884480) (by decide) (join_su (m := 207749120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 228884480) (by decide) (join_su (m := 209059840) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 209059840) (by decide) (leaf_ok cell13) (leaf_ok cell14)))) (join_su (m := 208404480) (by decide) (join_sr (m := 234455040) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_sr (m := 234455040) (by decide) (leaf_ok cell17) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (69/256 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

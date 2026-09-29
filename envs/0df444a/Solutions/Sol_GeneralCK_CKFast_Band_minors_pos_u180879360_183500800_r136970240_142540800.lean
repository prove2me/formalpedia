-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u180879360_183500800_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:26:15.465158+00:00
-- url     : https://prove2.me/submissions/5d592d3c-eab3-4fdb-b49c-313e362e36c8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [69/320, 7/32]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 180879360 181534720 136970240 138362880 ⟨⟨64559862131, 64559862137⟩, ⟨62842280669, 66289548708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 180879360 181534720 138362880 139755520 ⟨⟨65180934774, 65180934780⟩, ⟨63461124028, 66912851285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 181534720 182190080 136970240 138362880 ⟨⟨64285320323, 64285320327⟩, ⟨62572383079, 66010306602⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 181534720 182190080 138362880 139755520 ⟨⟨64903993458, 64903993460⟩, ⟨63188832678, 66631204028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 180879360 181534720 139755520 141148160 ⟨⟨65801435910, 65801435917⟩, ⟨64079399028, 67535579175⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 180879360 181534720 141148160 142540800 ⟨⟨66421367412, 66421367418⟩, ⟨64697107532, 68157734259⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 181534720 182190080 139755520 141148160 ⟨⟨65522101526, 65522101531⟩, ⟨63804720312, 67251533262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 181534720 182190080 141148160 142540800 ⟨⟨66139646378, 66139646382⟩, ⟨64420047815, 67871296159⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 182190080 182845440 136970240 138362880 ⟨⟨64011933438, 64011933444⟩, ⟨62303611381, 65732248921⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 182190080 182845440 138362880 139755520 ⟨⟨64628214459, 64628214465⟩, ⟨62917674614, 66350748595⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 182845440 183500800 136970240 138362880 ⟨⟨63739691389, 63739691396⟩, ⟨62035955757, 65455365297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 182845440 183500800 138362880 139755520 ⟨⟨64353587644, 64353587650⟩, ⟨62647639971, 66071474567⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 182190080 182845440 139755520 141148160 ⟨⟨65243936791, 65243936797⟩, ⟨63531182210, 66968686503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 182190080 182845440 141148160 142540800 ⟨⟨65859102254, 65859102260⟩, ⟨64144135972, 67586064474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 182845440 183500800 139755520 141148160 ⟨⟨64966931521, 64966931527⟩, ⟨63258774805, 66687028432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 182845440 183500800 141148160 142540800 ⟨⟨65579724810, 65579724817⟩, ⟨63869362039, 67302028692⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 180879360 183500800 136970240 142540800 t = true :=
  ⟨_, (join_su (m := 182190080) (by decide) (join_sr (m := 139755520) (by decide) (join_su (m := 181534720) (by decide) (join_sr (m := 138362880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 138362880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 181534720) (by decide) (join_sr (m := 141148160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 141148160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 139755520) (by decide) (join_su (m := 182845440) (by decide) (join_sr (m := 138362880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 138362880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 182845440) (by decide) (join_sr (m := 141148160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 141148160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (69/320 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((180879360 : ℤ) : ℝ) / (D : ℝ)) = (69/320 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

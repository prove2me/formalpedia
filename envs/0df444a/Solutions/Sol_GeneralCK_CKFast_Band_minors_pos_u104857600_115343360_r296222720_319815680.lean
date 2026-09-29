-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_115343360_r296222720_319815680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:40:32.064718+00:00
-- url     : https://prove2.me/submissions/44389799-2220-4e05-ba4b-da2e567d2cd4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 11/80]`, `ρ ∈ [113/320, 61/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 107479040 296222720 302120960 ⟨⟨207594190185, 207594190197⟩, ⟨196412575738, 219094028685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 104857600 107479040 302120960 308019200 ⟨⟨210900469519, 210900469530⟩, ⟨199692952390, 222423552746⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 107479040 110100480 296222720 302120960 ⟨⟨204295818907, 204295818916⟩, ⟨193278298319, 215625339165⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 107479040 110100480 302120960 308019200 ⟨⟨207570028260, 207570028271⟩, ⟨196525758274, 218923807593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 104857600 107479040 308019200 313917440 ⟨⟨214187015995, 214187016006⟩, ⟨202954042243, 225732910087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 104857600 107479040 313917440 319815680 ⟨⟨217454231341, 217454231351⟩, ⟨206196232904, 229022516542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 107479040 110100480 308019200 313917440 ⟨⟨210825153045, 210825153057⟩, ⟨199754569800, 222202765048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 107479040 110100480 313917440 319815680 ⟨⟨214061575508, 214061575517⟩, ⟨202965101756, 225462607186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 110100480 112721920 296222720 302120960 ⟨⟨201065758624, 201065758631⟩, ⟨190207511664, 212229978497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 110100480 112721920 302120960 308019200 ⟨⟨204307776747, 204307776753⟩, ⟨193422007048, 215497187164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 112721920 115343360 296222720 302120960 ⟨⟨197901350584, 197901350593⟩, ⟨187197768846, 208905068169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 112721920 115343360 302120960 308019200 ⟨⟨201111081213, 201111081224⟩, ⟨190379271697, 212140843625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 110100480 112721920 308019200 313917440 ⟨⟨207531341258, 207531341263⟩, ⟨196618474514, 218745524066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 110100480 112721920 313917440 319815680 ⟨⟨210736815838, 210736815845⟩, ⟨199797265070, 221975365613⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 112721920 115343360 308019200 313917440 ⟨⟨204302972077, 204302972088⟩, ⟨193543349609, 215358370073⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 112721920 115343360 313917440 319815680 ⟨⟨207477369175, 207477369186⟩, ⟨196690336593, 218558005577⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 115343360 296222720 319815680 t = true :=
  ⟨_, (join_su (m := 110100480) (by decide) (join_sr (m := 308019200) (by decide) (join_su (m := 107479040) (by decide) (join_sr (m := 302120960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 302120960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 107479040) (by decide) (join_sr (m := 313917440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 313917440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 308019200) (by decide) (join_su (m := 112721920) (by decide) (join_sr (m := 302120960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 302120960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 112721920) (by decide) (join_sr (m := 313917440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 313917440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (113/320 : ℝ) (61/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  have e3 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

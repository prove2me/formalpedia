-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_183500800_r226099200_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:19:14.59069+00:00
-- url     : https://prove2.me/submissions/3127441b-08d9-43ce-9cd9-32b958698ba0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 7/32]`, `ρ ∈ [69/256, 181/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 179568640 226099200 228884480 ⟨⟨104996728821, 104996728828⟩, ⟨101263240428, 108779258544⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178257920 179568640 228884480 231669760 ⟨⟨106186107862, 106186107870⟩, ⟨102444386328, 109976857751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 179568640 180879360 226099200 228884480 ⟨⟨104153004859, 104153004863⟩, ⟨100439445819, 107915209077⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 179568640 180879360 228884480 231669760 ⟨⟨105334198735, 105334198738⟩, ⟨101612429800, 109104601956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 178257920 179568640 231669760 234455040 ⟨⟨107373569250, 107373569256⟩, ⟨103623635169, 111172518283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 178257920 179568640 234455040 237240320 ⟨⟨108559125413, 108559125420⟩, ⟨104800999229, 112366252732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 179568640 180879360 231669760 234455040 ⟨⟨106513514678, 106513514679⟩, ⟨102783555851, 110292096480⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 179568640 180879360 234455040 237240320 ⟨⟨107690964771, 107690964775⟩, ⟨103952835904, 111477704890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 180879360 182190080 226099200 228884480 ⟨⟨103315446827, 103315446835⟩, ⟨99621588596, 107057559847⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 180879360 182190080 228884480 231669760 ⟨⟨104488486324, 104488486331⟩, ⟨100786441914, 108238776656⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 182190080 183500800 226099200 228884480 ⟨⟨102483956948, 102483956956⟩, ⟨98809574910, 106206209022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 182190080 183500800 228884480 231669760 ⟨⟨103648872647, 103648872655⟩, ⟨99966328595, 107379279839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 180879360 182190080 231669760 234455040 ⟨⟨105659686890, 105659686896⟩, ⟨101949475721, 109418134702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 180879360 182190080 234455040 237240320 ⟨⟨106829060274, 106829060282⟩, ⟨103110701621, 110595645881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 182190080 183500800 231669760 234455040 ⟨⟨104811987713, 104811987720⟩, ⟨101121300493, 108550530766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 182190080 183500800 234455040 237240320 ⟨⟨105973313567, 105973313573⟩, ⟨102274501887, 109719973368⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 183500800 226099200 237240320 t = true :=
  ⟨_, (join_su (m := 180879360) (by decide) (join_sr (m := 231669760) (by decide) (join_su (m := 179568640) (by decide) (join_sr (m := 228884480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 228884480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 179568640) (by decide) (join_sr (m := 234455040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 234455040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 231669760) (by decide) (join_su (m := 182190080) (by decide) (join_sr (m := 228884480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 228884480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 182190080) (by decide) (join_sr (m := 234455040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 234455040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (69/256 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

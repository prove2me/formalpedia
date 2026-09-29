-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_235929600_r315228160_326369280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:32:38.964047+00:00
-- url     : https://prove2.me/submissions/f306fc36-0b2a-4694-8223-39702c6c1938

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 9/32]`, `ρ ∈ [481/1280, 249/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231997440 315228160 318013440 ⟨⟨103153174928, 103153174934⟩, ⟨99845982060, 106498251645⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 231997440 318013440 320798720 ⟨⟨104013784120, 104013784127⟩, ⟨100699630676, 107365852416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231997440 233308160 315228160 318013440 ⟨⟨102276030796, 102276030798⟩, ⟨98982890372, 105606846674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231997440 233308160 318013440 320798720 ⟨⟨103130063414, 103130063417⟩, ⟨99829986592, 106467847514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 231997440 320798720 323584000 ⟨⟨104873726423, 104873726431⟩, ⟨101552615921, 108232782575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230686720 231997440 323584000 326369280 ⟨⟨105733005266, 105733005273⟩, ⟨102404941200, 109099045570⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231997440 233308160 320798720 323584000 ⟨⟨103983444557, 103983444560⟩, ⟨100676434644, 107328193371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 231997440 233308160 323584000 326369280 ⟨⟨104836177558, 104836177561⟩, ⟨101522237837, 108187887599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 234618880 315228160 318013440 ⟨⟨101402808807, 101402808813⟩, ⟨98123602930, 104719483928⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 233308160 234618880 318013440 320798720 ⟨⟨102250276704, 102250276711⟩, ⟨98964158819, 105573896460⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 234618880 235929600 315228160 318013440 ⟨⟨100533456732, 100533456738⟩, ⟨97268069029, 103836109614⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 234618880 235929600 318013440 320798720 ⟨⟨101374371706, 101374371712⟩, ⟨98102096583, 104683945414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 233308160 234618880 320798720 323584000 ⟨⟨103097108268, 103097108275⟩, ⟨99804081471, 106427669363⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 233308160 234618880 323584000 326369280 ⟨⟨103943306737, 103943306744⟩, ⟨100643374105, 107280805892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 234618880 235929600 320798720 323584000 ⟨⟨102214665216, 102214665223⟩, ⟨98935505568, 105531156661⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 234618880 235929600 323584000 326369280 ⟨⟨103054340409, 103054340417⟩, ⟨99768299112, 106377746520⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 235929600 315228160 326369280 t = true :=
  ⟨_, (join_su (m := 233308160) (by decide) (join_sr (m := 320798720) (by decide) (join_su (m := 231997440) (by decide) (join_sr (m := 318013440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 318013440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 231997440) (by decide) (join_sr (m := 323584000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 323584000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 320798720) (by decide) (join_su (m := 234618880) (by decide) (join_sr (m := 318013440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 318013440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 234618880) (by decide) (join_sr (m := 323584000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 323584000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (481/1280 : ℝ) (249/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((315228160 : ℤ) : ℝ) / (D : ℝ)) = (481/1280 : ℝ) := by norm_num [D]
  have e3 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

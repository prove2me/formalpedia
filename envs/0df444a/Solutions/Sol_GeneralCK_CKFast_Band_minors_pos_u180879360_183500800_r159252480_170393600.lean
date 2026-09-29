-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u180879360_183500800_r159252480_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:45:06.026332+00:00
-- url     : https://prove2.me/submissions/9433d67a-c328-4741-9b54-4ddaddf8f5d0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [69/320, 7/32]`, `ρ ∈ [243/1280, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 180879360 181534720 159252480 162037760 ⟨⟨74735622707, 74735622714⟩, ⟨72605558731, 76883908906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 181534720 182190080 159252480 162037760 ⟨⟨74422295493, 74422295498⟩, ⟨72298778036, 76563943395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 180879360 181534720 162037760 164823040 ⟨⟨75958837389, 75958837395⟩, ⟨73823950568, 78111937315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 181534720 182190080 162037760 164823040 ⟨⟨75640922594, 75640922596⟩, ⟨73512594056, 77787372868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 182190080 182845440 159252480 162037760 ⟨⟨74110236884, 74110236892⟩, ⟨71993227544, 76245285638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 182845440 183500800 159252480 162037760 ⟨⟨73799436083, 73799436089⟩, ⟨71688896806, 75927924466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 182190080 182845440 162037760 164823040 ⟨⟨75324289020, 75324289026⟩, ⟨73202480384, 77464128761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 182845440 183500800 162037760 164823040 ⟨⟨75008925793, 75008925799⟩, ⟨72893599032, 77142193753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 180879360 181534720 164823040 167608320 ⟨⟨77179893226, 77179893232⟩, ⟨75040199227, 79337791075⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 181534720 182190080 164823040 167608320 ⟨⟨76857414686, 76857414691⟩, ⟨74724290495, 79008651772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 180879360 181534720 167608320 170393600 ⟨⟨78398804235, 78398804243⟩, ⟨76254318594, 80561484334⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 181534720 182190080 167608320 170393600 ⟨⟨78071785581, 78071785586⟩, ⟨75933881035, 80227794038⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 182190080 182845440 164823040 167608320 ⟨⟨76536229745, 76536229752⟩, ⟨74409637006, 78680845149⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 182845440 183500800 164823040 167608320 ⟨⟨76216327457, 76216327463⟩, ⟨74096228167, 78354359899⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 182190080 182845440 167608320 170393600 ⟨⟨77746072663, 77746072670⟩, ⟨75614710889, 79895448525⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 182845440 183500800 167608320 170393600 ⟨⟨77421654466, 77421654473⟩, ⟨75296797488, 79564436419⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 180879360 183500800 159252480 170393600 t = true :=
  ⟨_, (join_sr (m := 164823040) (by decide) (join_su (m := 182190080) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 181534720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 181534720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 162037760) (by decide) (join_su (m := 182845440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 182845440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 182190080) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 181534720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 181534720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 167608320) (by decide) (join_su (m := 182845440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 182845440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (69/320 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((180879360 : ℤ) : ℝ) / (D : ℝ)) = (69/320 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u222822400_225443840_r164823040_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:13:52.620689+00:00
-- url     : https://prove2.me/submissions/c94acba0-252a-4fa7-8922-5d2c4f8897d3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/64, 43/160]`, `ρ ∈ [503/2560, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 222822400 223477760 164823040 166215680 ⟨⟨58519088062, 58519088068⟩, ⟨57012426735, 60035126453⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 222822400 223477760 166215680 167608320 ⟨⟨58994414020, 58994414027⟩, ⟨57485894393, 60512315483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 223477760 224133120 164823040 166215680 ⟨⟨58262322113, 58262322119⟩, ⟨56758983160, 59775004627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 223477760 224133120 166215680 167608320 ⟨⟨58735700373, 58735700380⟩, ⟨57230507886, 60250241236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 222822400 223477760 167608320 169000960 ⟨⟨59469484160, 59469484166⟩, ⟨57959107079, 60989247832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 222822400 223477760 169000960 170393600 ⟨⟨59944299135, 59944299140⟩, ⟨58432065445, 61465924157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 223477760 224133120 167608320 169000960 ⟨⟨59208825906, 59208825913⟩, ⟨57701780710, 60725224278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 223477760 224133120 169000960 170393600 ⟨⟨59681699357, 59681699364⟩, ⟨58172802275, 61199954398⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 224133120 224788480 164823040 166215680 ⟨⟨58006329225, 58006329227⟩, ⟨56506295754, 59515672979⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 224133120 224788480 166215680 167608320 ⟨⟨58477763996, 58477763997⟩, ⟨56975881749, 59988961380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 224788480 225443840 164823040 166215680 ⟨⟨57751103536, 57751103542⟩, ⟨56254358790, 59257125522⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 224788480 225443840 166215680 167608320 ⟨⟨58220599000, 58220599007⟩, ⟨56722010232, 59728469904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 224133120 224788480 167608320 169000960 ⟨⟨58948949099, 58948949102⟩, ⟨57445218882, 60461999296⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 224133120 224788480 169000960 170393600 ⟨⟨59419885172, 59419885175⟩, ⟨57914307788, 60934787362⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224788480 225443840 167608320 169000960 ⟨⟨58689847827, 58689847833⟩, ⟨57189415822, 60199566850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 224788480 225443840 169000960 170393600 ⟨⟨59158850643, 59158850648⟩, ⟨57656576183, 60670416986⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 222822400 225443840 164823040 170393600 t = true :=
  ⟨_, (join_su (m := 224133120) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 223477760) (by decide) (join_sr (m := 166215680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 166215680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 223477760) (by decide) (join_sr (m := 169000960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 169000960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 167608320) (by decide) (join_su (m := 224788480) (by decide) (join_sr (m := 166215680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 166215680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 224788480) (by decide) (join_sr (m := 169000960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 169000960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/64 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (503/2560 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u155975680_157286400_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:03:46.104721+00:00
-- url     : https://prove2.me/submissions/c64b9f7f-effe-4401-9389-148f85ebad03

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [119/640, 3/16]`, `ρ ∈ [1/10, 137/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 155975680 156303360 83886080 85360640 ⟨⟨47971261435, 47971261443⟩, ⟨46813244030, 49135338685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 156303360 156631040 83886080 85360640 ⟨⟨47863048207, 47863048212⟩, ⟨46707084697, 49025051957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 155975680 156303360 85360640 86835200 ⟨⟨48770702706, 48770702712⟩, ⟨47611045308, 49936416203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 156303360 156631040 85360640 86835200 ⟨⟨48660827787, 48660827790⟩, ⟨47503227300, 49824464823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 156631040 156958720 83886080 85360640 ⟨⟨47755135009, 47755135015⟩, ⟨46601218004, 48915072755⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 156958720 157286400 83886080 85360640 ⟨⟨47647520275, 47647520281⟩, ⟨46495642427, 48805399463⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 156631040 156958720 85360640 86835200 ⟨⟨48551256689, 48551256695⟩, ⟨47395705716, 49712824765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 156958720 157286400 85360640 86835200 ⟨⟨48441987830, 48441987836⟩, ⟨47288479019, 49601494395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 155975680 156303360 86835200 88309760 ⟨⟨49569000446, 49569000454⟩, ⟨48407708362, 50736344873⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 156303360 156631040 86835200 88309760 ⟨⟨49457470593, 49457470596⟩, ⟨48298238389, 50622735638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 155975680 156303360 88309760 89784320 ⟨⟨50366159538, 50366159544⟩, ⟨49203238037, 51535129604⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 156303360 156631040 88309760 89784320 ⟨⟨50252981461, 50252981465⟩, ⟨49092122774, 51419869267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 156631040 156958720 86835200 88309760 ⟨⟨49346248309, 49346248316⟩, ⟨48189068589, 50509441479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 156958720 157286400 86835200 88309760 ⟨⟨49235331998, 49235332006⟩, ⟨48080197406, 50396460745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 156631040 156958720 88309760 89784320 ⟨⟨50140114666, 50140114672⟩, ⟨48981311387, 51304927721⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 156958720 157286400 88309760 89784320 ⟨⟨50027557536, 50027557543⟩, ⟨48870802309, 51190303298⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 155975680 157286400 83886080 89784320 t = true :=
  ⟨_, (join_sr (m := 86835200) (by decide) (join_su (m := 156631040) (by decide) (join_sr (m := 85360640) (by decide) (join_su (m := 156303360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 156303360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 85360640) (by decide) (join_su (m := 156958720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 156958720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 156631040) (by decide) (join_sr (m := 88309760) (by decide) (join_su (m := 156303360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 156303360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 88309760) (by decide) (join_su (m := 156958720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 156958720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (119/640 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((155975680 : ℤ) : ℝ) / (D : ℝ)) = (119/640 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

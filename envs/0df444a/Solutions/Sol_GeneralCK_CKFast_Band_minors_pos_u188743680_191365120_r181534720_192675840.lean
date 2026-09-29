-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_191365120_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:05:12.256394+00:00
-- url     : https://prove2.me/submissions/eadae67b-f4c5-42ae-93eb-b90178c92691

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 73/320]`, `ρ ∈ [277/1280, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 189399040 181534720 184320000 ⟨⟨80356727816, 80356727824⟩, ⟨78265678625, 82464904612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 189399040 190054400 181534720 184320000 ⟨⟨80022989192, 80022989198⟩, ⟨77938138349, 82124886957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 188743680 189399040 184320000 187105280 ⟨⟨81510926041, 81510926049⟩, ⟨79415297636, 83623676443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 189399040 190054400 184320000 187105280 ⟨⟨81172910489, 81172910495⟩, ⟨79083490816, 83279371826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 190054400 190709760 181534720 184320000 ⟨⟨79690485098, 79690485105⟩, ⟨77611798355, 81786138691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 190709760 191365120 181534720 184320000 ⟨⟨79359205532, 79359205539⟩, ⟨77286648936, 81448649510⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 190054400 190709760 184320000 187105280 ⟨⟨80836139595, 80836139601⟩, ⟨78752894429, 82936346691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 190709760 191365120 184320000 187105280 ⟨⟨80500603299, 80500603306⟩, ⟨78423498719, 82594590675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 188743680 189399040 187105280 189890560 ⟨⟨82663327480, 82663327488⟩, ⟨80563132081, 84780639148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 189399040 190054400 187105280 189890560 ⟨⟨82321054751, 82321054759⟩, ⟨80227078274, 84432067509⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 188743680 189399040 189890560 192675840 ⟨⟨83813943210, 83813943216⟩, ⟨81709192943, 85935803891⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 189399040 190054400 189890560 192675840 ⟨⟨83467432891, 83467432897⟩, ⟨81368911548, 85582985011⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 190054400 190709760 187105280 189890560 ⟨⟨81980036613, 81980036621⟩, ⟨79892244866, 84084785251⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 190709760 191365120 187105280 189890560 ⟨⟨81640262957, 81640262965⟩, ⟨79558622049, 83738781957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 190054400 190709760 189890560 192675840 ⟨⟨83122186908, 83122186914⟩, ⟨81029860332, 85231465213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 190709760 191365120 189890560 192675840 ⟨⟨82778195100, 82778195106⟩, ⟨80692029430, 84881234036⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 191365120 181534720 192675840 t = true :=
  ⟨_, (join_sr (m := 187105280) (by decide) (join_su (m := 190054400) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 189399040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 189399040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184320000) (by decide) (join_su (m := 190709760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 190709760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 190054400) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 189399040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 189399040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 189890560) (by decide) (join_su (m := 190709760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 190709760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (73/320 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((191365120 : ℤ) : ℝ) / (D : ℝ)) = (73/320 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

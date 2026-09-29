-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_117964800_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:19:47.763202+00:00
-- url     : https://prove2.me/submissions/a9a00624-f70a-48e3-bbf1-363b15408813

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 9/64]`, `ρ ∈ [91/640, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 115343360 115998720 119275520 122224640 ⟨⟨89110300594, 89110300604⟩, ⟨86054812065, 92202460194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 115998720 116654080 119275520 122224640 ⟨⟨88682488779, 88682488785⟩, ⟨85640826870, 91760533041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 115343360 115998720 122224640 125173760 ⟨⟨91078307438, 91078307445⟩, ⟨88015927311, 94177226563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 115998720 116654080 122224640 125173760 ⟨⟨90642684656, 90642684658⟩, ⟨87594137065, 93727485258⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 116654080 117309440 119275520 122224640 ⟨⟨88257703378, 88257703387⟩, ⟨85229740988, 91321763000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 117309440 117964800 119275520 122224640 ⟨⟨87835906684, 87835906693⟩, ⟨84821518503, 90886110501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 116654080 117309440 122224640 125173760 ⟨⟨90210124368, 90210124376⟩, ⟨87175282646, 93280936660⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 117309440 117964800 122224640 125173760 ⟨⟨89780588613, 89780588620⟩, ⟨86759327865, 92837540957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 115343360 115998720 125173760 128122880 ⟨⟨93038005484, 93038005494⟩, ⟨89968821701, 96143596251⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 115998720 116654080 125173760 128122880 ⟨⟨92594667652, 92594667657⟩, ⟨89539321115, 95686137908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 115343360 115998720 128122880 131072000 ⟨⟨94989489321, 94989489329⟩, ⟨91913588259, 98101665419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 115998720 116654080 128122880 131072000 ⟨⟨94538530741, 94538530746⟩, ⟨91476470458, 97636585501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 116654080 117309440 125173760 128122880 ⟨⟨92154427204, 92154427212⟩, ⟨89112791688, 95231906658⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 117309440 117964800 125173760 128122880 ⟨⟨91717245936, 91717245944⟩, ⟨88689196981, 94780862468⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 116654080 117309440 128122880 131072000 ⟨⟨94090703271, 94090703278⟩, ⟨91042358001, 97174765887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 117309440 117964800 128122880 131072000 ⟨⟨93645968483, 93645968492⟩, ⟨90611214212, 96716166337⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 117964800 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 116654080) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 115998720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 115998720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 122224640) (by decide) (join_su (m := 117309440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 117309440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 116654080) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 115998720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 115998720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 128122880) (by decide) (join_su (m := 117309440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 117309440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (9/64 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((117964800 : ℤ) : ℝ) / (D : ℝ)) = (9/64 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

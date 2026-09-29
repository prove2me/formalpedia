-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_67108864_r596377600_644874240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:21:39.755791+00:00
-- url     : https://prove2.me/submissions/6566543b-05d3-4d8c-a7a6-a9b57c5d0d64

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 2/25]`, `ρ ∈ [91/128, 123/160]` by 9 cells of the computing
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
theorem cell0 : cellOK 50331648 54525952 596377600 620625920 ⟨⟨466556174356, 466556174364⟩, ⟨433172959929, 500733339412⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 54525952 58720256 596377600 620625920 ⟨⟨457065759222, 457065759240⟩, ⟨424354502257, 490592524301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 50331648 54525952 620625920 644874240 ⟨⟨478121151802, 478121151812⟩, ⟨444939609502, 512007901622⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 54525952 58720256 620625920 644874240 ⟨⟨468624390549, 468624390564⟩, ⟨436082869277, 501896556635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 58720256 62914560 596377600 620625920 ⟨⟨447846977495, 447846977510⟩, ⟨415783523555, 480743840651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 62914560 67108864 596377600 608501760 ⟨⟨435977912999, 435977913013⟩, ⟨411627694742, 460865167606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 62914560 67108864 608501760 620625920 ⟨⟨441773244194, 441773244208⟩, ⟨417447778019, 466612953451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 58720256 62914560 620625920 644874240 ⟨⟨459388851720, 459388851735⟩, ⟨427465382892, 492064668697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 62914560 67108864 620625920 644874240 ⟨⟨450395960521, 450395960536⟩, ⟨419070460977, 482492278168⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 67108864 596377600 644874240 t = true :=
  ⟨_, (join_su (m := 58720256) (by decide) (join_sr (m := 620625920) (by decide) (join_su (m := 54525952) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 54525952) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 620625920) (by decide) (join_su (m := 62914560) (by decide) (leaf_ok cell4) (join_sr (m := 608501760) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 62914560) (by decide) (leaf_ok cell7) (leaf_ok cell8))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (91/128 : ℝ) (123/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((596377600 : ℤ) : ℝ) / (D : ℝ)) = (91/128 : ℝ) := by norm_num [D]
  have e3 : (((644874240 : ℤ) : ℝ) / (D : ℝ)) = (123/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

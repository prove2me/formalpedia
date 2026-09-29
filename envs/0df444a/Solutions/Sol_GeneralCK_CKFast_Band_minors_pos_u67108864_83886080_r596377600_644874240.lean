-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_83886080_r596377600_644874240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:58:41.257377+00:00
-- url     : https://prove2.me/submissions/8f4ef84b-b48d-4d6e-977f-08a1ca76f35c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 1/10]`, `ρ ∈ [91/128, 123/160]` by 15 cells of the computing
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
theorem cell0 : cellOK 67108864 71303168 596377600 608501760 ⟨⟨427255656495, 427255656510⟩, ⟨403345752393, 451710309409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 67108864 71303168 608501760 620625920 ⟨⟨433032804319, 433032804332⟩, ⟨409137842288, 457450840932⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 71303168 75497472 596377600 608501760 ⟨⟨418755441686, 418755441700⟩, ⟨395270725939, 442791137701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 71303168 75497472 608501760 620625920 ⟨⟨424510251517, 424510251531⟩, ⟨401031337750, 448519555038⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 67108864 71303168 620625920 644874240 ⟨⟨441629372138, 441629372152⟩, ⟨410883334220, 473161872753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 71303168 75497472 620625920 632750080 ⟨⟨430228572542, 430228572556⟩, ⟨406755345409, 454211917527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 71303168 75497472 632750080 644874240 ⟨⟨435912098249, 435912098265⟩, ⟨412444410918, 459869933337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 75497472 79691776 596377600 608501760 ⟨⟨410463535809, 410463535823⟩, ⟨387390003586, 434092999656⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 75497472 79691776 608501760 620625920 ⟨⟨416192168042, 416192168055⟩, ⟨393115921199, 439804804248⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 79691776 83886080 596377600 608501760 ⟨⟨402367576197, 402367576211⟩, ⟨379692194247, 425602727630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 79691776 83886080 608501760 620625920 ⟨⟨408066476468, 408066476484⟩, ⟨385380444789, 431293748260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 75497472 79691776 620625920 632750080 ⟨⟨421885062704, 421885062717⟩, ⟨398806138014, 445481111457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 75497472 79691776 632750080 644874240 ⟨⟨427543851516, 427543851530⟩, ⟨404462250310, 451123573895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 79691776 83886080 620625920 632750080 ⟨⟨413730443729, 413730443744⟩, ⟨391033929710, 436949907307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 79691776 83886080 632750080 644874240 ⟨⟨419361047568, 419361047582⟩, ⟨396654180189, 442572800204⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 83886080 596377600 644874240 t = true :=
  ⟨_, (join_su (m := 75497472) (by decide) (join_sr (m := 620625920) (by decide) (join_su (m := 71303168) (by decide) (join_sr (m := 608501760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 608501760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 71303168) (by decide) (leaf_ok cell4) (join_sr (m := 632750080) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 620625920) (by decide) (join_su (m := 79691776) (by decide) (join_sr (m := 608501760) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 608501760) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 79691776) (by decide) (join_sr (m := 632750080) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 632750080) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (91/128 : ℝ) (123/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((596377600 : ℤ) : ℝ) / (D : ℝ)) = (91/128 : ℝ) := by norm_num [D]
  have e3 : (((644874240 : ℤ) : ℝ) / (D : ℝ)) = (123/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

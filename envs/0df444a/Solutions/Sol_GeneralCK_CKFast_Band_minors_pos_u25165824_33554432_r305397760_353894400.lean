-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u25165824_33554432_r305397760_353894400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:32:08.263635+00:00
-- url     : https://prove2.me/submissions/2ceabaca-4460-43f3-962b-ad4a24cb9658

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/100, 1/25]`, `ρ ∈ [233/640, 27/64]` by 13 cells of the computing
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
theorem cell0 : cellOK 25165824 27262976 305397760 317521920 ⟨⟨375068771965, 375068771976⟩, ⟨351176358864, 399774060135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 27262976 29360128 305397760 317521920 ⟨⟨368303736787, 368303736805⟩, ⟨344951298060, 392453778980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 25165824 27262976 317521920 329646080 ⟨⟨382775463226, 382775463232⟩, ⟨359155012194, 407157362469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 27262976 29360128 317521920 329646080 ⟨⟨376045211682, 376045211699⟩, ⟨352942698252, 399896537192⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 29360128 31457280 305397760 317521920 ⟨⟨361784813895, 361784813911⟩, ⟨338946852994, 385404959014⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 31457280 33554432 305397760 317521920 ⟨⟨355494573532, 355494573550⟩, ⟨333147791298, 378608109890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 29360128 31457280 317521920 329646080 ⟨⟨369553526355, 369553526371⟩, ⟨346945044600, 392897886366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 31457280 33554432 317521920 329646080 ⟨⟨363283687776, 363283687790⟩, ⟨341147386693, 386142782019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 25165824 29360128 329646080 341770240 ⟨⟨386942808482, 386942808501⟩, ⟨352718789867, 422763124152⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 25165824 29360128 341770240 353894400 ⟨⟨394355815872, 394355815891⟩, ⟨360434886264, 429777435151⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 29360128 31457280 329646080 341770240 ⟨⟨377161515160, 377161515179⟩, ⟨354775434607, 400240136592⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 31457280 33554432 329646080 341770240 ⟨⟨370913120151, 370913120170⟩, ⟨348981256455, 393526547549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 29360128 33554432 341770240 353894400 ⟨⟨381481378733, 381481378751⟩, ⟨348908689596, 415524998968⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 25165824 33554432 305397760 353894400 t = true :=
  ⟨_, (join_sr (m := 329646080) (by decide) (join_su (m := 29360128) (by decide) (join_sr (m := 317521920) (by decide) (join_su (m := 27262976) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 27262976) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 317521920) (by decide) (join_su (m := 31457280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 31457280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 29360128) (by decide) (join_sr (m := 341770240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 341770240) (by decide) (join_su (m := 31457280) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/100 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (233/640 : ℝ) (27/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((305397760 : ℤ) : ℝ) / (D : ℝ)) = (233/640 : ℝ) := by norm_num [D]
  have e3 : (((353894400 : ℤ) : ℝ) / (D : ℝ)) = (27/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

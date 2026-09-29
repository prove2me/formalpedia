-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_212336640_r170393600_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:20:01.222538+00:00
-- url     : https://prove2.me/submissions/66340b88-2d54-47e4-b16a-cde9f47502ca

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 81/320]`, `ρ ∈ [13/64, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 210370560 170393600 173178880 ⟨⟨66142112402, 66142112408⟩, ⟨64250813474, 68048216250⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 210370560 211025920 170393600 173178880 ⟨⟨65859432635, 65859432641⟩, ⟨63973324315, 67760281052⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 209715200 210370560 173178880 175964160 ⟨⟨67169290042, 67169290047⟩, ⟨65273725188, 69079663401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 210370560 211025920 173178880 175964160 ⟨⟨66882573183, 66882573190⟩, ⟨64992210352, 68787679906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 211025920 211681280 170393600 173178880 ⟨⟨65577675841, 65577675844⟩, ⟨63696731974, 67473295435⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 211681280 212336640 170393600 173178880 ⟨⟨65296834871, 65296834878⟩, ⟨63421029519, 67187252038⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 211025920 211681280 173178880 175964160 ⟨⟨66596788401, 66596788404⟩, ⟨64711601435, 68496655093⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 211681280 212336640 173178880 175964160 ⟨⟨66311928493, 66311928500⟩, ⟨64431891451, 68206581550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 209715200 210370560 175964160 178749440 ⟨⟨68195188267, 68195188273⟩, ⟨66295364767, 70109823766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 210370560 211025920 175964160 178749440 ⟨⟨67904449167, 67904449172⟩, ⟨66009838968, 69813806958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 209715200 210370560 178749440 181534720 ⟨⟨69219814094, 69219814100⟩, ⟨67315739180, 71138704407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 210370560 211025920 178749440 181534720 ⟨⟨68925067495, 68925067501⟩, ⟨67026217027, 70838669165⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 211025920 211681280 175964160 178749440 ⟨⟨67614651098, 67614651099⟩, ⟨65725228043, 69518757786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 211681280 212336640 175964160 178749440 ⟨⟨67325786806, 67325786812⟩, ⟨65441524952, 69224668785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 211025920 211681280 178749440 181534720 ⟨⟨68631270735, 68631270738⟩, ⟨66737618556, 70539610364⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 211681280 212336640 178749440 181534720 ⟨⟨68338416513, 68338416518⟩, ⟨66449936679, 70241520491⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 212336640 170393600 181534720 t = true :=
  ⟨_, (join_sr (m := 175964160) (by decide) (join_su (m := 211025920) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 210370560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 210370560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 173178880) (by decide) (join_su (m := 211681280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 211681280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 211025920) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 210370560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 210370560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178749440) (by decide) (join_su (m := 211681280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 211681280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (81/320 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

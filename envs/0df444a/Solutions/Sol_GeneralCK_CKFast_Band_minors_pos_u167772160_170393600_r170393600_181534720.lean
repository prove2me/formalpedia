-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_170393600_r170393600_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:37:15.587865+00:00
-- url     : https://prove2.me/submissions/4a31987c-05e5-451b-9e4a-14020ba2d30a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 13/64]`, `ρ ∈ [13/64, 277/1280]` by 12 cells of the computing
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
theorem cell0 : cellOK 167772160 168427520 170393600 173178880 ⟨⟨86541184897, 86541184905⟩, ⟨84251457156, 88851062988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 168427520 169082880 170393600 173178880 ⟨⟨86180771697, 86180771702⟩, ⟨83898482857, 88483104681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 167772160 168427520 173178880 175964160 ⟨⟨87848270305, 87848270313⟩, ⟨85553574778, 90163096739⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 168427520 169082880 173178880 175964160 ⟨⟨87483116253, 87483116256⟩, ⟨85195869422, 89790388349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 169082880 169738240 170393600 173178880 ⟨⟨85821925361, 85821925368⟩, ⟨83547029109, 88116760448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 169738240 170393600 170393600 173178880 ⟨⟨85464632061, 85464632068⟩, ⟨83197082533, 87752015997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 169082880 169738240 173178880 175964160 ⟨⟨87119542075, 87119542083⟩, ⟨84839697700, 89419306967⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 169738240 170393600 173178880 175964160 ⟨⟨86757533880, 86757533886⟩, ⟨84485046158, 89049838236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 167772160 169082880 175964160 178749440 ⟨⟨88967607086, 88967607092⟩, ⟨85221811505, 92766329493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 167772160 169082880 178749440 181534720 ⟨⟨90267136295, 90267136302⟩, ⟨86512437663, 94074738461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 169082880 170393600 175964160 178749440 ⟨⟨88231055205, 88231055211⟩, ⟨84506706360, 92007837771⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 169082880 170393600 178749440 181534720 ⟨⟨89521239463, 89521239469⟩, ⟨85788020245, 93306871652⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 170393600 170393600 181534720 t = true :=
  ⟨_, (join_sr (m := 175964160) (by decide) (join_su (m := 169082880) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 168427520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 168427520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 173178880) (by decide) (join_su (m := 169738240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 169738240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 169082880) (by decide) (join_sr (m := 178749440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 178749440) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (13/64 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

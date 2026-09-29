-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_178257920_r794296320_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:26:59.372017+00:00
-- url     : https://prove2.me/submissions/640e4242-42b2-4e37-8558-40d5c7e5c8cb

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 17/80]`, `ρ ∈ [303/320, 1]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 170393600 794296320 805437440 ⟨⟨337764572732, 337764572743⟩, ⟨325416692790, 350324280146⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 170393600 173015040 794296320 805437440 ⟨⟨333645318002, 333645318013⟩, ⟨321397543358, 346105482216⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 167772160 170393600 805437440 816578560 ⟨⟨341793854124, 341793854135⟩, ⟨329397107448, 354399850129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 170393600 173015040 805437440 816578560 ⟨⟨337640899754, 337640899765⟩, ⟨325343614661, 350148108732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 173015040 175636480 794296320 805437440 ⟨⟨329547934896, 329547934908⟩, ⟨317399609229, 341909148867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 175636480 178257920 794296320 805437440 ⟨⟨325471960471, 325471960477⟩, ⟨313422435363, 337734811276⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 173015040 175636480 805437440 816578560 ⟨⟨333509465538, 333509465549⟩, ⟨321311021951, 345918442093⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 175636480 178257920 805437440 816578560 ⟨⟨329399097581, 329399097585⟩, ⟨317298882519, 341710391255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 167772160 170393600 816578560 827719680 ⟨⟨345816102013, 345816102024⟩, ⟨333370626747, 358468221279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 170393600 173015040 816578560 827719680 ⟨⟨341629633307, 341629633319⟩, ⟨329282972488, 354183724863⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 167772160 170393600 827719680 838860800 ⟨⟨349831638194, 349831638205⟩, ⟨337337564372, 362529722987⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 170393600 173015040 827719680 838860800 ⟨⟨345611830337, 345611830348⟩, ⟨333215920647, 358212649655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 173015040 175636480 816578560 827719680 ⟨⟨337464331640, 337464331651⟩, ⟨325215901126, 349920912107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 175636480 178257920 816578560 827719680 ⟨⟨333319752044, 333319752050⟩, ⟨321168974007, 345679333768⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 173015040 175636480 827719680 838860800 ⟨⟨341412834951, 341412834962⟩, ⟨329114540884, 353916867801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 175636480 178257920 827719680 838860800 ⟨⟨337234215881, 337234215889⟩, ⟨325032994478, 349641937755⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 178257920 794296320 838860800 t = true :=
  ⟨_, (join_sr (m := 816578560) (by decide) (join_su (m := 173015040) (by decide) (join_sr (m := 805437440) (by decide) (join_su (m := 170393600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 170393600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 805437440) (by decide) (join_su (m := 175636480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 175636480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 173015040) (by decide) (join_sr (m := 827719680) (by decide) (join_su (m := 170393600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 170393600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 827719680) (by decide) (join_su (m := 175636480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 175636480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (303/320 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((794296320 : ℤ) : ℝ) / (D : ℝ)) = (303/320 : ℝ) := by norm_num [D]
  have e3 : (((838860800 : ℤ) : ℝ) / (D : ℝ)) = (1 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

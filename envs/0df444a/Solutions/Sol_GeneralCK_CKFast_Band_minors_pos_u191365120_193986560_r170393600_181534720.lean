-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u191365120_193986560_r170393600_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:05:33.12756+00:00
-- url     : https://prove2.me/submissions/bdf52958-ae22-4fb8-b0da-aff6135fbc0e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [73/320, 37/160]`, `ρ ∈ [13/64, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 191365120 192020480 170393600 173178880 ⟨⟨74463135939, 74463135942⟩, ⟨72414942317, 76528153881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 192020480 192675840 170393600 173178880 ⟨⟨74151415842, 74151415848⟩, ⟨72109241524, 76210334903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 191365120 192020480 173178880 175964160 ⟨⟨75607268452, 75607268455⟩, ⟨73554490574, 77676866877⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 192020480 192675840 173178880 175964160 ⟨⟨75291234074, 75291234080⟩, ⟨73244486737, 77354722701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 192675840 193331200 170393600 173178880 ⟨⟨73840849310, 73840849317⟩, ⟨71804661141, 75893703245⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 193331200 193986560 170393600 173178880 ⟨⟨73531426962, 73531426967⟩, ⟨71501192075, 75578249229⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 192675840 193331200 173178880 175964160 ⟨⟨74976363936, 74976363944⟩, ⟨72935614003, 77033776500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 193331200 193986560 173178880 175964160 ⟨⟨74662648599, 74662648605⟩, ⟨72627863219, 76714018536⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 191365120 192020480 175964160 178749440 ⟨⟨76749639602, 76749639604⟩, ⟨74692289281, 78823806573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 192020480 192675840 175964160 178749440 ⟨⟨76429310564, 76429310570⟩, ⟨74378001834, 78497357012⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 191365120 192020480 178749440 181534720 ⟨⟨77890260101, 77890260104⟩, ⟨75828349066, 79968983771⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 192020480 192675840 178749440 181534720 ⟨⟨77565655867, 77565655874⟩, ⟨75509797285, 79638248477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 192675840 193331200 175964160 178749440 ⟨⟨76110156251, 76110156257⟩, ⟨74064855991, 78172115883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 193331200 193986560 175964160 178749440 ⟨⟨75792167161, 75792167167⟩, ⟨73752842542, 77848073394⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 192675840 193331200 178749440 181534720 ⟨⟨77242236649, 77242236655⟩, ⟨75192397419, 79308731879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 193331200 193986560 178749440 181534720 ⟨⟨76919992888, 76919992893⟩, ⟨74876140202, 78980424129⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 191365120 193986560 170393600 181534720 t = true :=
  ⟨_, (join_sr (m := 175964160) (by decide) (join_su (m := 192675840) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 192020480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 192020480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 173178880) (by decide) (join_su (m := 193331200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 193331200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 192675840) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 192020480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 192020480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178749440) (by decide) (join_su (m := 193331200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 193331200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (73/320 : ℝ) (37/160 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((191365120 : ℤ) : ℝ) / (D : ℝ)) = (73/320 : ℝ) := by norm_num [D]
  have e1 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

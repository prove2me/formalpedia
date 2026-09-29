-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u191365120_193986560_r159252480_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:41:34.428405+00:00
-- url     : https://prove2.me/submissions/190b4be9-a441-4fa9-9fd2-54d72e04a25c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [73/320, 37/160]`, `ρ ∈ [243/1280, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 191365120 192020480 159252480 162037760 ⟨⟨69868775510, 69868775513⟩, ⟨67839038827, 71915350389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 192020480 192675840 159252480 162037760 ⟨⟨69574512013, 69574512020⟩, ⟨67550747748, 71615033619⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 191365120 192020480 162037760 164823040 ⟨⟨71020062030, 71020062031⟩, ⟨68985692946, 73071266023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 192020480 192675840 162037760 164823040 ⟨⟨70721404133, 70721404139⟩, ⟨68693019482, 72766543156⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 192675840 193331200 159252480 162037760 ⟨⟨69281357386, 69281357393⟩, ⟨67263532342, 71315859536⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 193331200 193986560 159252480 162037760 ⟨⟨68989302507, 68989302514⟩, ⟨66977383778, 71017818722⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 192675840 193331200 162037760 164823040 ⟨⟨70423866583, 70423866589⟩, ⟨68401433175, 72462974442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 193331200 193986560 162037760 164823040 ⟨⟨70127440191, 70127440197⟩, ⟨68110925127, 72160550392⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 191365120 192020480 164823040 167608320 ⟨⟨72169543619, 72169543622⟩, ⟨70130554305, 74225364434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 192020480 192675840 164823040 167608320 ⟨⟨71866511599, 71866511607⟩, ⟨69833518537, 73916255947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 191365120 192020480 167608320 170393600 ⟨⟨73317231280, 73317231283⟩, ⟨71273633816, 75377656716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 192020480 192675840 167608320 170393600 ⟨⟨73009845249, 73009845255⟩, ⟨70972255660, 75064182911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 192675840 193331200 164823040 167608320 ⟨⟨71564611200, 71564611206⟩, ⟨69537581207, 73608312869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 193331200 193986560 164823040 167608320 ⟨⟨71263833164, 71263833172⟩, ⟨69242733352, 73301525648⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 192675840 193331200 167608320 170393600 ⟨⟨72703601910, 72703601916⟩, ⟨70671987024, 74751885574⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 193331200 193986560 167608320 170393600 ⟨⟨72398491942, 72398491948⟩, ⟨70372818883, 74440755085⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 191365120 193986560 159252480 170393600 t = true :=
  ⟨_, (join_sr (m := 164823040) (by decide) (join_su (m := 192675840) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 192020480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 192020480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 162037760) (by decide) (join_su (m := 193331200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 193331200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 192675840) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 192020480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 192020480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 167608320) (by decide) (join_su (m := 193331200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 193331200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (73/320 : ℝ) (37/160 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((191365120 : ℤ) : ℝ) / (D : ℝ)) = (73/320 : ℝ) := by norm_num [D]
  have e1 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

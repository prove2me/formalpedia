-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_115343360_r272629760_296222720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:42:40.951991+00:00
-- url     : https://prove2.me/submissions/92b27c4a-a3a0-4717-bc26-3ecee685e4cc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 11/80]`, `ρ ∈ [13/40, 113/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 107479040 272629760 278528000 ⟨⟨194163349475, 194163349486⟩, ⟨183090107221, 205565569194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 104857600 107479040 278528000 284426240 ⟨⟨197552784441, 197552784451⟩, ⟨186451703427, 208980136393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 107479040 110100480 272629760 278528000 ⟨⟨191000155643, 191000155654⟩, ⟨180094278813, 202228089793⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 107479040 110100480 278528000 284426240 ⟨⟨194354718275, 194354718286⟩, ⟨183420203818, 205608761325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 104857600 107479040 284426240 290324480 ⟨⟨200920775280, 200920775292⟩, ⟨189792363435, 212372763623⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 104857600 107479040 290324480 296222720 ⟨⟨204267766185, 204267766197⟩, ⟨193112515108, 215743911455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 107479040 110100480 284426240 290324480 ⟨⟨197688570266, 197688570275⟩, ⟨186725912827, 208968237057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 107479040 110100480 290324480 296222720 ⟨⟨201002133354, 201002133363⟩, ⟨190011812164, 212306954234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 110100480 112721920 272629760 278528000 ⟨⟨187905564343, 187905564349⟩, ⟨177161934554, 198964569680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 110100480 112721920 278528000 284426240 ⟨⟨191225212926, 191225212931⟩, ⟨180452221803, 202311218047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 112721920 115343360 272629760 278528000 ⟨⟨184876820028, 184876820039⟩, ⟨174290552074, 195772009503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 112721920 115343360 278528000 284426240 ⟨⟨188161536462, 188161536473⟩, ⟨177545253138, 199084537040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 110100480 112721920 284426240 290324480 ⟨⟨194524862828, 194524862836⟩, ⟨183722991348, 205637393950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 110100480 112721920 290324480 296222720 ⟨⟨197804914470, 197804914473⟩, ⟨186974629057, 208943512459⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 112721920 115343360 284426240 290324480 ⟨⟨191426945082, 191426945092⟩, ⟨180781113404, 202377294895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 112721920 115343360 290324480 296222720 ⟨⟨194673426053, 194673426062⟩, ⟨183998499321, 205650677078⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 115343360 272629760 296222720 t = true :=
  ⟨_, (join_su (m := 110100480) (by decide) (join_sr (m := 284426240) (by decide) (join_su (m := 107479040) (by decide) (join_sr (m := 278528000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 278528000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 107479040) (by decide) (join_sr (m := 290324480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 290324480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 284426240) (by decide) (join_su (m := 112721920) (by decide) (join_sr (m := 278528000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 278528000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 112721920) (by decide) (join_sr (m := 290324480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 290324480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (13/40 : ℝ) (113/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  have e3 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

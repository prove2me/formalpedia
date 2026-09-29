-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_235929600_r660602880_682885120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:51:45.252128+00:00
-- url     : https://prove2.me/submissions/9d169e82-7e03-4e7f-86a2-668c44a92de0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 9/32]`, `ρ ∈ [63/80, 521/640]` by 12 cells of the computing
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
theorem cell0 : cellOK 230686720 233308160 660602880 666173440 ⟨⟨205339946671, 205339946680⟩, ⟨197089417049, 213750505282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 233308160 666173440 671744000 ⟨⟨206935517999, 206935518007⟩, ⟨198658302054, 215372787505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233308160 234618880 660602880 666173440 ⟨⟨202939288558, 202939288567⟩, ⟨198231124088, 207700974153⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 234618880 235929600 660602880 666173440 ⟨⟨201343661828, 201343661837⟩, ⟨196656803634, 206083882072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 233308160 234618880 666173440 671744000 ⟨⟨204519062643, 204519062652⟩, ⟨199796872329, 209294756539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 234618880 235929600 666173440 671744000 ⟨⟨202912882690, 202912882698⟩, ⟨198212012617, 207667100859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 230686720 233308160 671744000 677314560 ⟨⟨208529842035, 208529842044⟩, ⟨200225946865, 216993811261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 230686720 233308160 677314560 682885120 ⟨⟨210122937138, 210122937147⟩, ⟨201792369550, 218613595182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 234618880 671744000 677314560 ⟨⟨206097627778, 206097627787⟩, ⟨201361417990, 210887322420⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 234618880 235929600 671744000 677314560 ⟨⟨204480919736, 204480919745⟩, ⟨199766043678, 209249128775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 233308160 234618880 677314560 682885120 ⟨⟨207675001691, 207675001700⟩, ⟨202924778620, 212478689702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 234618880 235929600 677314560 682885120 ⟨⟨206047790288, 206047790298⟩, ⟨201318913960, 210829983311⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 235929600 660602880 682885120 t = true :=
  ⟨_, (join_sr (m := 671744000) (by decide) (join_su (m := 233308160) (by decide) (join_sr (m := 666173440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 666173440) (by decide) (join_su (m := 234618880) (by decide) (leaf_ok cell2) (leaf_ok cell3)) (join_su (m := 234618880) (by decide) (leaf_ok cell4) (leaf_ok cell5)))) (join_su (m := 233308160) (by decide) (join_sr (m := 677314560) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 677314560) (by decide) (join_su (m := 234618880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 234618880) (by decide) (leaf_ok cell10) (leaf_ok cell11)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (63/80 : ℝ) (521/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((660602880 : ℤ) : ℝ) / (D : ℝ)) = (63/80 : ℝ) := by norm_num [D]
  have e3 : (((682885120 : ℤ) : ℝ) / (D : ℝ)) = (521/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

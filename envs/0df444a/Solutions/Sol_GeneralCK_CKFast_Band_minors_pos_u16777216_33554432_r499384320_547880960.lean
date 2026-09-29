-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_33554432_r499384320_547880960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:33:39.855479+00:00
-- url     : https://prove2.me/submissions/87581e59-db05-41fd-b174-72737573d2f8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 1/25]`, `ρ ∈ [381/640, 209/320]` by 9 cells of the computing
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
theorem cell0 : cellOK 16777216 20971520 499384320 523632640 ⟨⟨510109853968, 510109853986⟩, ⟨467315565639, 553830129294⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 20971520 25165824 499384320 523632640 ⟨⟨496555799120, 496555799138⟩, ⟨455121331830, 539007490915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 16777216 20971520 523632640 547880960 ⟨⟨521869663960, 521869663978⟩, ⟨479797529824, 564698164089⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 20971520 25165824 523632640 547880960 ⟨⟨508475887913, 508475887928⟩, ⟨467680056486, 550127183726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 25165824 29360128 499384320 523632640 ⟨⟨483772017600, 483772017618⟩, ⟨443575427028, 525048011688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 29360128 33554432 499384320 511508480 ⟨⟨468573501505, 468573501521⟩, ⟨438695759167, 499129563838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 29360128 33554432 511508480 523632640 ⟨⟨474705308554, 474705308571⟩, ⟨444996096087, 505049279280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 25165824 29360128 523632640 547880960 ⟨⟨495819152249, 495819152267⟩, ⟨456186125912, 536377632136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 29360128 33554432 523632640 547880960 ⟨⟨483792647389, 483792647403⟩, ⟨445235676397, 523326341424⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 33554432 499384320 547880960 t = true :=
  ⟨_, (join_su (m := 25165824) (by decide) (join_sr (m := 523632640) (by decide) (join_su (m := 20971520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 20971520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 523632640) (by decide) (join_su (m := 29360128) (by decide) (leaf_ok cell4) (join_sr (m := 511508480) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 29360128) (by decide) (leaf_ok cell7) (leaf_ok cell8))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (381/640 : ℝ) (209/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((499384320 : ℤ) : ℝ) / (D : ℝ)) = (381/640 : ℝ) := by norm_num [D]
  have e3 : (((547880960 : ℤ) : ℝ) / (D : ℝ)) = (209/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_180879360_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:26:08.764298+00:00
-- url     : https://prove2.me/submissions/752a7615-84dd-4d5e-ad96-e23628013696

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 69/320]`, `ρ ∈ [87/512, 113/640]` by 8 cells of the computing
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
theorem cell0 : cellOK 178257920 178913280 142540800 145326080 ⟨⟨68503443803, 68503443806⟩, ⟨66376377719, 70649168677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178913280 179568640 142540800 145326080 ⟨⟨68213298671, 68213298679⟩, ⟨66092861043, 70352297677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 178257920 178913280 145326080 148111360 ⟨⟨69758995541, 69758995544⟩, ⟨67626956951, 71909682968⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 178913280 179568640 145326080 148111360 ⟨⟨69464057827, 69464057834⟩, ⟨67338660910, 71608006601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 179568640 180224000 142540800 145326080 ⟨⟨67924383605, 67924383611⟩, ⟨65810534444, 70056697540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 180224000 180879360 142540800 145326080 ⟨⟨67636687826, 67636687833⟩, ⟨65529387527, 69762357101⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 179568640 180224000 145326080 148111360 ⟨⟨69170364672, 69170364679⟩, ⟨67051569450, 71307615571⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 180224000 180879360 145326080 148111360 ⟨⟨68877905207, 68877905213⟩, ⟨66765672085, 71008498625⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 180879360 142540800 148111360 t = true :=
  ⟨_, (join_su (m := 179568640) (by decide) (join_sr (m := 145326080) (by decide) (join_su (m := 178913280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 178913280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 145326080) (by decide) (join_su (m := 180224000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 180224000) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (69/320 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((180879360 : ℤ) : ℝ) / (D : ℝ)) = (69/320 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

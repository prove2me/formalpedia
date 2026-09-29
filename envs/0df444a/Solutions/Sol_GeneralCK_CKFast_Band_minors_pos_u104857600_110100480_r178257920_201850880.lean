-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_110100480_r178257920_201850880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:29:09.034111+00:00
-- url     : https://prove2.me/submissions/c935b3ab-3a01-42d1-8828-a2796e1d7779

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 21/160]`, `ρ ∈ [17/80, 77/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 106168320 178257920 184156160 ⟨⟨137234879871, 137234879879⟩, ⟨130452671851, 144169066298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 106168320 107479040 178257920 184156160 ⟨⟨135976311184, 135976311195⟩, ⟨129256267197, 142846100886⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 104857600 106168320 184156160 190054400 ⟨⟨141051377737, 141051377747⟩, ⟨134248716565, 148004632739⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 106168320 107479040 184156160 190054400 ⟨⟨139767447625, 139767447633⟩, ⟨133026761047, 146656546643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 107479040 108789760 178257920 184156160 ⟨⟨134734622806, 134734622813⟩, ⟨128075629464, 141541180380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 108789760 110100480 178257920 184156160 ⟨⟨133509413688, 133509413698⟩, ⟨126910387801, 140253871964⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 107479040 108789760 184156160 190054400 ⟨⟨138500525888, 138500525895⟩, ⟨131820714570, 145326617557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 108789760 110100480 184156160 190054400 ⟨⟨137250212314, 137250212322⟩, ⟨130630206441, 144014414252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 104857600 106168320 190054400 195952640 ⟨⟨144837109230, 144837109241⟩, ⟨138014567644, 151808868548⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 106168320 107479040 190054400 195952640 ⟨⟨143528448429, 143528448440⟩, ⟨136767680218, 150436303482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 104857600 106168320 195952640 201850880 ⟨⟨148592775208, 148592775218⟩, ⟨141750904714, 155582495927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 106168320 107479040 195952640 201850880 ⟨⟨147259993060, 147259993069⟩, ⟨140479683695, 154186071446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 107479040 108789760 190054400 195952640 ⟨⟨142236911012, 142236911019⟩, ⟨135536831017, 149081994388⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 108789760 110100480 190054400 195952640 ⟨⟨140962097878, 140962097889⟩, ⟨134321649796, 147745511905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 107479040 108789760 195952640 201850880 ⟨⟨145944436930, 145944436937⟩, ⟨139224617817, 152807989483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 108789760 110100480 195952640 201850880 ⟨⟨144645709102, 144645709111⟩, ⟨137985337559, 151447822791⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 110100480 178257920 201850880 t = true :=
  ⟨_, (join_sr (m := 190054400) (by decide) (join_su (m := 107479040) (by decide) (join_sr (m := 184156160) (by decide) (join_su (m := 106168320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 106168320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184156160) (by decide) (join_su (m := 108789760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 108789760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 107479040) (by decide) (join_sr (m := 195952640) (by decide) (join_su (m := 106168320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 106168320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 195952640) (by decide) (join_su (m := 108789760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 108789760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (21/160 : ℝ) →
    rho ∈ Set.Icc (17/80 : ℝ) (77/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e2 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e3 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

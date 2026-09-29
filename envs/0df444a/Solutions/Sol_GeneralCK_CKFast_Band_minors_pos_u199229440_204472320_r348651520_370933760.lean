-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_204472320_r348651520_370933760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:44:00.166568+00:00
-- url     : https://prove2.me/submissions/415d97f4-1613-473c-9819-ca2fa6883ed5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 39/160]`, `ρ ∈ [133/320, 283/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 200540160 348651520 354222080 ⟨⟨138228494993, 138228494995⟩, ⟨133754734962, 142764875044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 200540160 201850880 348651520 354222080 ⟨⟨137155064577, 137155064584⟩, ⟨132705461497, 141666858063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 199229440 200540160 354222080 359792640 ⟨⟨140244375507, 140244375511⟩, ⟨135754854047, 144796464343⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 200540160 201850880 354222080 359792640 ⟨⟨139157777216, 139157777224⟩, ⟨134692440583, 143685256508⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 201850880 203161600 348651520 354222080 ⟨⟨136087205718, 136087205725⟩, ⟨131661551028, 140574625588⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 203161600 204472320 348651520 354222080 ⟨⟨135024843498, 135024843505⟩, ⟨130622931504, 139488099782⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 201850880 203161600 354222080 359792640 ⟨⟨138076766362, 138076766371⟩, ⟨133635407326, 142579847613⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 203161600 204472320 354222080 359792640 ⟨⟨137001268158, 137001268164⟩, ⟨132583682316, 141480159988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 199229440 200540160 359792640 365363200 ⟨⟨142256083167, 142256083171⟩, ⟨137750848945, 146823830637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 200540160 201850880 359792640 365363200 ⟨⟨141156401113, 141156401120⟩, ⟨136675378135, 145699517530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 199229440 200540160 365363200 370933760 ⟨⟨144263667322, 144263667326⟩, ⟨139742768330, 148847023952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 200540160 201850880 365363200 370933760 ⟨⟨143150984359, 143150984366⟩, ⟨138654321597, 147709689876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 201850880 203161600 359792640 365363200 ⟨⟨140062321060, 140062321066⟩, ⟨135605303449, 144581016460⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 203161600 204472320 359792640 365363200 ⟨⟨138973768361, 138973768369⟩, ⟨134540553032, 143468249941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 201850880 203161600 365363200 370933760 ⟨⟨142043916674, 142043916682⟩, ⟨137571285640, 146578179627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 203161600 204472320 365363200 370933760 ⟨⟨140942389781, 140942389790⟩, ⟨136493588722, 145452415917⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 204472320 348651520 370933760 t = true :=
  ⟨_, (join_sr (m := 359792640) (by decide) (join_su (m := 201850880) (by decide) (join_sr (m := 354222080) (by decide) (join_su (m := 200540160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 200540160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 354222080) (by decide) (join_su (m := 203161600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 203161600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 201850880) (by decide) (join_sr (m := 365363200) (by decide) (join_su (m := 200540160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 200540160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 365363200) (by decide) (join_su (m := 203161600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 203161600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (133/320 : ℝ) (283/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  have e3 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

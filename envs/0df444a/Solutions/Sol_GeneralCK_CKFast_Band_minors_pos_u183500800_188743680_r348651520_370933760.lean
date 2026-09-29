-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u183500800_188743680_r348651520_370933760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:47:05.351364+00:00
-- url     : https://prove2.me/submissions/a0657da2-b644-4689-b46f-f8abbc1083b9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/32, 9/40]`, `ρ ∈ [133/320, 283/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 183500800 184811520 348651520 354222080 ⟨⟨151573223414, 151573223421⟩, ⟨146792195540, 156422392755⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 184811520 186122240 348651520 354222080 ⟨⟨150426628306, 150426628313⟩, ⟨145672503639, 155248407028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 183500800 184811520 354222080 359792640 ⟨⟨153748296738, 153748296747⟩, ⟨148951292288, 158613321135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 184811520 186122240 354222080 359792640 ⟨⟨152588356926, 152588356933⟩, ⟨147818264164, 157425988744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 186122240 187432960 348651520 354222080 ⟨⟨149286604997, 149286605000⟩, ⟨144559136179, 154081245655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 187432960 188743680 348651520 354222080 ⟨⟨148153062319, 148153062326⟩, ⟨143452005577, 152920813814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 186122240 187432960 354222080 359792640 ⟨⟨151435002425, 151435002429⟩, ⟨146691575879, 156245492179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 187432960 188743680 354222080 359792640 ⟨⟨150288142330, 150288142339⟩, ⟨145571140062, 155071736941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 183500800 184811520 359792640 365363200 ⟨⟨155918079210, 155918079217⟩, ⟨151105166050, 160798889213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 184811520 186122240 359792640 365363200 ⟨⟨154744895896, 154744895903⟩, ⟨149958901187, 159598313084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 183500800 184811520 365363200 370933760 ⟨⟨158082637707, 158082637714⟩, ⟨153253882672, 162979164914⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 184811520 186122240 365363200 370933760 ⟨⟨156896310445, 156896310453⟩, ⟨152094478940, 161765446283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 186122240 187432960 359792640 365363200 ⟨⟨153578309887, 153578309892⟩, ⟨148818990064, 158404582714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 187432960 188743680 359792640 365363200 ⟨⟨152418230561, 152418230570⟩, ⟨147685345539, 157217603942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 186122240 187432960 365363200 370933760 ⟨⟨155716590999, 155716591003⟩, ⟨150941441384, 160558581844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 187432960 188743680 365363200 370933760 ⟨⟨154543389046, 154543389053⟩, ⟨149794683112, 159358477791⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 183500800 188743680 348651520 370933760 t = true :=
  ⟨_, (join_sr (m := 359792640) (by decide) (join_su (m := 186122240) (by decide) (join_sr (m := 354222080) (by decide) (join_su (m := 184811520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 184811520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 354222080) (by decide) (join_su (m := 187432960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 187432960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 186122240) (by decide) (join_sr (m := 365363200) (by decide) (join_su (m := 184811520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 184811520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 365363200) (by decide) (join_su (m := 187432960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 187432960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/32 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (133/320 : ℝ) (283/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  have e3 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

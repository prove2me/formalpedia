-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_125829120_r296222720_319815680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:43:16.750327+00:00
-- url     : https://prove2.me/submissions/f11c125e-5cc7-443d-9127-ab2b371a1c81

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 3/20]`, `ρ ∈ [113/320, 61/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 115343360 117964800 296222720 302120960 ⟨⟨194800075749, 194800075760⟩, ⟨184246750248, 205647882131⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 115343360 117964800 302120960 308019200 ⟨⟨197977445370, 197977445380⟩, ⟨187395250657, 208852078925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 117964800 120586240 296222720 302120960 ⟨⟨191759545241, 191759545251⟩, ⟨181352254920, 202455836325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 117964800 120586240 302120960 308019200 ⟨⟨194904501032, 194904501042⟩, ⟨184467759340, 205628334560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 115343360 117964800 308019200 313917440 ⟨⟨201137572209, 201137572220⟩, ⟨190526911919, 212038633148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 115343360 117964800 313917440 319815680 ⟨⟨204280785427, 204280785436⟩, ⟨193642051848, 215207885392⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 117964800 120586240 308019200 313917440 ⟨⟨198032794441, 198032794450⟩, ⟨187566993558, 208783780526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 117964800 120586240 313917440 319815680 ⟨⟨201144738581, 201144738590⟩, ⟨190650259980, 211922498154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 120586240 123207680 296222720 302120960 ⟨⟨188777491601, 188777491610⟩, ⟨178512192691, 199326479083⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 120586240 123207680 302120960 308019200 ⟨⟨191889999573, 191889999581⟩, ⟨181594722383, 202467182201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 123207680 125829120 296222720 302120960 ⟨⟨185851760772, 185851760778⟩, ⟨175724576905, 196257482337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 123207680 125829120 302120960 308019200 ⟨⟨188931804059, 188931804066⟩, ⟨178774166539, 199366315067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 120586240 123207680 308019200 313917440 ⟨⟨194986409261, 194986409272⟩, ⟨184661534346, 205591407402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 120586240 123207680 313917440 319815680 ⟨⟨198067018503, 198067018513⟩, ⟨187712916303, 208699462756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 123207680 125829120 308019200 313917440 ⟨⟨191996297170, 191996297177⟩, ⟨181808574801, 202459228525⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 123207680 125829120 313917440 319815680 ⟨⟨195045523392, 195045523398⟩, ⟨184828075440, 205536515660⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 125829120 296222720 319815680 t = true :=
  ⟨_, (join_su (m := 120586240) (by decide) (join_sr (m := 308019200) (by decide) (join_su (m := 117964800) (by decide) (join_sr (m := 302120960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 302120960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 117964800) (by decide) (join_sr (m := 313917440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 313917440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 308019200) (by decide) (join_su (m := 123207680) (by decide) (join_sr (m := 302120960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 302120960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 123207680) (by decide) (join_sr (m := 313917440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 313917440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (113/320 : ℝ) (61/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  have e3 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

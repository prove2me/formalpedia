-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u138936320_141557760_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:19:06.489277+00:00
-- url     : https://prove2.me/submissions/31275ff4-299e-4a3a-8f2a-835ed390547f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [53/320, 27/160]`, `ρ ∈ [91/640, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 138936320 139591680 119275520 122224640 ⟨⟨75379174375, 75379174378⟩, ⟨72752470399, 78034048981⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 139591680 140247040 119275520 122224640 ⟨⟨75040384105, 75040384113⟩, ⟨72423861585, 77684887133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 138936320 139591680 122224640 125173760 ⟨⟨77086961352, 77086961354⟩, ⟨74453770953, 79748261326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 139591680 140247040 122224640 125173760 ⟨⟨76741506831, 76741506838⟩, ⟨74118512873, 79392421598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 140247040 140902400 119275520 122224640 ⟨⟨74703581492, 74703581500⟩, ⟨72097161327, 77337794071⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 140902400 141557760 119275520 122224640 ⟨⟨74368745056, 74368745064⟩, ⟨71772349105, 76992747329⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 140247040 140902400 122224640 125173760 ⟨⟨76398067675, 76398067682⟩, ⟨73785191176, 79038678222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 140902400 141557760 122224640 125173760 ⟨⟨76056622200, 76056622207⟩, ⟨73453785132, 78687008531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 138936320 139591680 125173760 128122880 ⟨⟨78789249356, 78789249359⟩, ⟨76149625572, 81456921467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 139591680 140247040 125173760 128122880 ⟨⟨78437192667, 78437192674⟩, ⟨75807779558, 81094466696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 138936320 139591680 128122880 131072000 ⟨⟨80486090043, 80486090046⟩, ⟨77840085188, 83160081791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 139591680 140247040 128122880 131072000 ⟨⟨80127492430, 80127492437⟩, ⟨77491711746, 82791073951⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 140247040 140902400 125173760 128122880 ⟨⟨78087178332, 78087178341⟩, ⟨75467897043, 80734135108⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 140902400 141557760 125173760 128122880 ⟨⟨77739184471, 77739184479⟩, ⟨75129957099, 80375903851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 140247040 140902400 128122880 131072000 ⟨⟨79770963453, 79770963461⟩, ⟨77145328225, 82424215414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 140902400 141557760 128122880 131072000 ⟨⟨79416481047, 79416481054⟩, ⟨76800913504, 82059483144⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 138936320 141557760 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 140247040) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 139591680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 139591680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 122224640) (by decide) (join_su (m := 140902400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 140902400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 140247040) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 139591680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 139591680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 128122880) (by decide) (join_su (m := 140902400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 140902400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (53/320 : ℝ) (27/160 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((138936320 : ℤ) : ℝ) / (D : ℝ)) = (53/320 : ℝ) := by norm_num [D]
  have e1 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

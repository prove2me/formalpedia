-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_193986560_r348651520_370933760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:41:53.496744+00:00
-- url     : https://prove2.me/submissions/8b783d2f-559b-4d54-8685-9cffbfcb9257

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 37/160]`, `ρ ∈ [133/320, 283/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 190054400 348651520 354222080 ⟨⟨147025910642, 147025910649⟩, ⟨142351025704, 151767018296⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 190054400 191365120 348651520 354222080 ⟨⟨145905061823, 145905061830⟩, ⟨141256111867, 150619767439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 188743680 190054400 354222080 359792640 ⟨⟨149147687267, 149147687275⟩, ⟨144456870782, 153904630127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 190054400 191365120 354222080 359792640 ⟨⟨148013549327, 148013549335⟩, ⟨143348683533, 152744080369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 191365120 192675840 348651520 354222080 ⟨⟨144790429185, 144790429192⟩, ⟨140167180765, 149478971119⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 192675840 193986560 348651520 354222080 ⟨⟨143681927476, 143681927478⟩, ⟨139084150461, 148344540697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 191365120 192675840 354222080 359792640 ⟨⟨146885642059, 146885642068⟩, ⟨142246495192, 151589997818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 192675840 193986560 354222080 359792640 ⟨⟨145763880424, 145763880429⟩, ⟨141150223983, 150442294103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 188743680 190054400 359792640 365363200 ⟨⟨151264568809, 151264568818⟩, ⟨146557881897, 156037284191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 190054400 191365120 359792640 365363200 ⟨⟨150117236982, 150117236990⟩, ⟨145436514836, 154863532404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 188743680 190054400 365363200 370933760 ⟨⟨153376615762, 153376615769⟩, ⟨148654118643, 158165041888⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 190054400 191365120 365363200 370933760 ⟨⟨152216183769, 152216183778⟩, ⟨147519663893, 156978183405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 191365120 192675840 359792640 365363200 ⟨⟨148976148867, 148976148876⟩, ⟨144321161426, 153696259026⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 192675840 193986560 359792640 365363200 ⟨⟨147841219657, 147841219661⟩, ⟨143211740075, 152535375966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 191365120 192675840 365363200 370933760 ⟨⟨151062007119, 151062007125⟩, ⟨146391236142, 155797813096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 192675840 193986560 365363200 370933760 ⟨⟨149914001244, 149914001248⟩, ⟨145268753999, 154623843170⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 193986560 348651520 370933760 t = true :=
  ⟨_, (join_sr (m := 359792640) (by decide) (join_su (m := 191365120) (by decide) (join_sr (m := 354222080) (by decide) (join_su (m := 190054400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 190054400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 354222080) (by decide) (join_su (m := 192675840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 192675840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 191365120) (by decide) (join_sr (m := 365363200) (by decide) (join_su (m := 190054400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 190054400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 365363200) (by decide) (join_su (m := 192675840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 192675840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (37/160 : ℝ) →
    rho ∈ Set.Icc (133/320 : ℝ) (283/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e2 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  have e3 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

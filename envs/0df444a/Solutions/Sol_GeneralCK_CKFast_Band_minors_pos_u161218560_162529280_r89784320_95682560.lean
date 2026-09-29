-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u161218560_162529280_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:17:27.320884+00:00
-- url     : https://prove2.me/submissions/3c7d19f5-6a66-4821-bc89-c4ae93a3b854

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [123/640, 31/160]`, `ρ ∈ [137/1280, 73/640]` by 13 cells of the computing
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
theorem cell0 : cellOK 161218560 161546240 89784320 91258880 ⟨⟨49361969902, 49361969903⟩, ⟨48229609653, 50500076181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 161546240 161873920 89784320 91258880 ⟨⟨49251999489, 49251999495⟩, ⟨48121591312, 50388135817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 161218560 161546240 91258880 92733440 ⟨⟨50131134654, 50131134658⟩, ⟨48997200632, 51270811695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 161546240 161873920 91258880 92733440 ⟨⟨50019585597, 50019585605⟩, ⟨48887606438, 51157289938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 161873920 162201600 89784320 91258880 ⟨⟨49142319171, 49142319177⟩, ⟨48013856294, 50276492401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 162201600 162529280 89784320 91258880 ⟨⟨49032927477, 49032927483⟩, ⟨47906403167, 50165144431⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 161873920 162201600 91258880 92733440 ⟨⟨49908330027, 49908330033⟩, ⟨48778298958, 51044068524⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 162201600 162529280 91258880 92733440 ⟨⟨49797366458, 49797366464⟩, ⟨48669276742, 50931145937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 161218560 161873920 92733440 94208000 ⟨⟨50842678085, 50842678091⟩, ⟨49024932735, 52674973795⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 161218560 161873920 94208000 95682560 ⟨⟨51609016715, 51609016721⟩, ⟨49788525053, 53444055783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 161873920 162201600 92733440 94208000 ⟨⟨50673329566, 50673329572⟩, ⟨49541734805, 51810628818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 162201600 162529280 92733440 94208000 ⟨⟨50560800045, 50560800053⟩, ⟨49431149390, 51696137573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 161873920 162529280 94208000 95682560 ⟨⟨51380239870, 51380239873⟩, ⟨49565321277, 53209624494⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 161218560 162529280 89784320 95682560 t = true :=
  ⟨_, (join_sr (m := 92733440) (by decide) (join_su (m := 161873920) (by decide) (join_sr (m := 91258880) (by decide) (join_su (m := 161546240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 161546240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 91258880) (by decide) (join_su (m := 162201600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 162201600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 161873920) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 94208000) (by decide) (join_su (m := 162201600) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (123/640 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((161218560 : ℤ) : ℝ) / (D : ℝ)) = (123/640 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

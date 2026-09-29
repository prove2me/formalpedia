-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u52428800_54525952_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:58:37.099396+00:00
-- url     : https://prove2.me/submissions/b0ec4fb0-5e26-422d-9c41-482da0cf7dbc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/16, 13/200]`, `ρ ∈ [229/2560, 133/1280]` by 11 cells of the computing
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
theorem cell0 : cellOK 52428800 52953088 75038720 78069760 ⟨⟨106781750716, 106781750731⟩, ⟨101815798881, 111846557618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 52953088 53477376 75038720 78069760 ⟨⟨106091754713, 106091754725⟩, ⟨101162816080, 111118228789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 52428800 53477376 78069760 81100800 ⟨⟨109939484359, 109939484374⟩, ⟨102760610567, 117326690555⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 53477376 54001664 75038720 78069760 ⟨⟨105410449706, 105410449721⟩, ⟨100517951990, 110399190534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 54001664 54525952 75038720 78069760 ⟨⟨104737659398, 104737659410⟩, ⟨99881043637, 109689252461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 53477376 54001664 78069760 81100800 ⟨⟨108890410383, 108890410395⟩, ⟨103992958203, 113882885726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 54001664 54525952 78069760 81100800 ⟨⟨108201837740, 108201837752⟩, ⟨103340100552, 113157361821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 52428800 53477376 81100800 84131840 ⟨⟨113402159538, 113402159550⟩, ⟨106214037534, 120796154450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 52428800 53477376 84131840 87162880 ⟨⟨116824738106, 116824738121⟩, ⟨109628134958, 124224786983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 53477376 54525952 81100800 84131840 ⟨⟨111977045545, 111977045560⟩, ⟨104890228761, 119264567411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 53477376 54525952 84131840 87162880 ⟨⟨115369978636, 115369978648⟩, ⟨108274205976, 122664146212⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 52428800 54525952 75038720 87162880 t = true :=
  ⟨_, (join_sr (m := 81100800) (by decide) (join_su (m := 53477376) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 52953088) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 78069760) (by decide) (join_su (m := 54001664) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (join_su (m := 54001664) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_su (m := 53477376) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 84131840) (by decide) (leaf_ok cell9) (leaf_ok cell10))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/16 : ℝ) (13/200 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((52428800 : ℤ) : ℝ) / (D : ℝ)) = (1/16 : ℝ) := by norm_num [D]
  have e1 : (((54525952 : ℤ) : ℝ) / (D : ℝ)) = (13/200 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

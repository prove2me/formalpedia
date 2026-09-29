-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u58720256_60817408_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:03:52.189193+00:00
-- url     : https://prove2.me/submissions/65d04e4c-521f-45f0-a8c7-45bd494ee4dc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/100, 29/400]`, `ρ ∈ [229/2560, 133/1280]` by 13 cells of the computing
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
theorem cell0 : cellOK 58720256 59244544 75038720 78069760 ⟨⟨99038892573, 99038892581⟩, ⟨94482068060, 103680382740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 59244544 59768832 75038720 78069760 ⟨⟨98442541858, 98442541869⟩, ⟨93916659450, 103052052898⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 58720256 59244544 78069760 81100800 ⟨⟨102365633379, 102365633387⟩, ⟨97802465662, 107012506164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 59244544 59768832 78069760 81100800 ⟨⟨101754513590, 101754513601⟩, ⟨97222179326, 106369537926⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 59768832 60293120 75038720 78069760 ⟨⟨97853052886, 97853052900⟩, ⟨93357676250, 102431040826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 60293120 60817408 75038720 78069760 ⟨⟨97270297846, 97270297857⟩, ⟨92804999938, 101817208912⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 59768832 60293120 78069760 81100800 ⟨⟨101150353725, 101150353739⟩, ⟨96648421282, 105733980323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 60293120 60817408 78069760 81100800 ⟨⟨100553025337, 100553025351⟩, ⟨96081072195, 105105695307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 58720256 59768832 81100800 84131840 ⟨⟨105343389386, 105343389397⟩, ⟨98720029570, 112144475708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 58720256 59768832 84131840 87162880 ⟨⟨108593258375, 108593258387⟩, ⟨101959086110, 115403338837⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 59768832 60293120 81100800 84131840 ⟨⟨104413175674, 104413175685⟩, ⟨99905150968, 109001988376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 60293120 60817408 81100800 84131840 ⟨⟨103801712383, 103801712397⟩, ⟨99323561291, 108359694544⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 59768832 60817408 84131840 87162880 ⟨⟨107328863451, 107328863465⟩, ⟨100779332188, 114050295242⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 58720256 60817408 75038720 87162880 t = true :=
  ⟨_, (join_sr (m := 81100800) (by decide) (join_su (m := 59768832) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 59244544) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 59244544) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 78069760) (by decide) (join_su (m := 60293120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 60293120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 59768832) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 84131840) (by decide) (join_su (m := 60293120) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/100 : ℝ) (29/400 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e1 : (((60817408 : ℤ) : ℝ) / (D : ℝ)) = (29/400 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

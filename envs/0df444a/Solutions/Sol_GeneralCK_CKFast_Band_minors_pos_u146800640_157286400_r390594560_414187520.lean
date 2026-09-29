-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_157286400_r390594560_414187520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:06:28.76402+00:00
-- url     : https://prove2.me/submissions/acf4b0a1-5c52-4a2e-9627-56c5cf3249e1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 3/16]`, `ρ ∈ [149/320, 79/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 149422080 390594560 396492800 ⟨⟨205116367605, 205116367615⟩, ⟨195583702230, 214873355169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 146800640 149422080 396492800 402391040 ⟨⟨207745073233, 207745073243⟩, ⟨198183144688, 217530393950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 149422080 152043520 390594560 396492800 ⟨⟨202188246214, 202188246219⟩, ⟨192759433242, 211838611978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 149422080 152043520 396492800 402391040 ⟨⟨204790516765, 204790516770⟩, ⟨195332188328, 214469532454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 146800640 149422080 402391040 408289280 ⟨⟨210365040460, 210365040470⟩, ⟨200774039409, 220178498802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 146800640 149422080 408289280 414187520 ⟨⟨212976407428, 212976407436⟩, ⟨203356520711, 222817811736⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 149422080 152043520 402391040 408289280 ⟨⟨207384335382, 207384335387⟩, ⟨197896675678, 217091811625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 149422080 152043520 408289280 414187520 ⟨⟨209969834096, 209969834100⟩, ⟨200453023707, 219705585186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 152043520 154664960 390594560 396492800 ⟨⟨199298705241, 199298705251⟩, ⟨189971627818, 208844621021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 152043520 154664960 396492800 402391040 ⟨⟨201874479716, 201874479726⟩, ⟨192517660544, 211449333424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 154664960 157286400 390594560 396492800 ⟨⟨196446621155, 196446621165⟩, ⟨187219228386, 205890191561⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 154664960 157286400 396492800 402391040 ⟨⟨198995846751, 198995846761⟩, ⟨189738510622, 208468615786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 152043520 154664960 402391040 408289280 ⟨⟨204442081697, 204442081707⟩, ⟨195055698504, 214045690173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 152043520 154664960 408289280 414187520 ⟨⟨207001637359, 207001637367⟩, ⟨197585864454, 216633820899⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 154664960 157286400 402391040 408289280 ⟨⟨201537172365, 201537172375⟩, ⟨192250064142, 211038963102⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 154664960 157286400 408289280 414187520 ⟨⟨204070718545, 204070718553⟩, ⟨194754006271, 213601357325⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 157286400 390594560 414187520 t = true :=
  ⟨_, (join_su (m := 152043520) (by decide) (join_sr (m := 402391040) (by decide) (join_su (m := 149422080) (by decide) (join_sr (m := 396492800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 396492800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 149422080) (by decide) (join_sr (m := 408289280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 408289280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 402391040) (by decide) (join_su (m := 154664960) (by decide) (join_sr (m := 396492800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 396492800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 154664960) (by decide) (join_sr (m := 408289280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 408289280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (149/320 : ℝ) (79/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((390594560 : ℤ) : ℝ) / (D : ℝ)) = (149/320 : ℝ) := by norm_num [D]
  have e3 : (((414187520 : ℤ) : ℝ) / (D : ℝ)) = (79/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

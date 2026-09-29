-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u73400320_75497472_r87162880_99287040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:29:52.622622+00:00
-- url     : https://prove2.me/submissions/aa30f33a-bd16-4a46-ae4d-0b6b3ecf4187

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/80, 9/100]`, `ρ ∈ [133/1280, 303/2560]` by 11 cells of the computing
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
theorem cell0 : cellOK 73400320 73924608 87162880 90193920 ⟨⟨96217444590, 96217444599⟩, ⟨92357600576, 100136923671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 73924608 74448896 87162880 90193920 ⟨⟨95726313437, 95726313447⟩, ⟨91887881761, 99623787762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 73400320 74448896 90193920 93224960 ⟨⟨98816552797, 98816552807⟩, ⟨93161799654, 104600134355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 74448896 74973184 87162880 90193920 ⟨⟨95239704054, 95239704064⟩, ⟨91422440601, 99115426856⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 74973184 75497472 87162880 90193920 ⟨⟨94757547825, 94757547834⟩, ⟨90961212705, 98611767929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 74448896 74973184 90193920 93224960 ⟨⟨98068285680, 98068285690⟩, ⟨94244112424, 101950432318⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 74973184 75497472 90193920 93224960 ⟨⟨97575099430, 97575099442⟩, ⟨93771817039, 101435790355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 73400320 74448896 93224960 96256000 ⟨⟨101638768305, 101638768315⟩, ⟨95972167969, 107433232720⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 73400320 74448896 96256000 99287040 ⟨⟨104438388876, 104438388886⟩, ⟨98760333733, 110243349888⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 74448896 75497472 93224960 96256000 ⟨⟨100621679199, 100621679211⟩, ⟨95014110757, 106354735155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 74448896 75497472 96256000 99287040 ⟨⟨103400131920, 103400131933⟩, ⟨97781003548, 109143827563⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 73400320 75497472 87162880 99287040 t = true :=
  ⟨_, (join_sr (m := 93224960) (by decide) (join_su (m := 74448896) (by decide) (join_sr (m := 90193920) (by decide) (join_su (m := 73924608) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 90193920) (by decide) (join_su (m := 74973184) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (join_su (m := 74973184) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_su (m := 74448896) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 96256000) (by decide) (leaf_ok cell9) (leaf_ok cell10))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/80 : ℝ) (9/100 : ℝ) →
    rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((73400320 : ℤ) : ℝ) / (D : ℝ)) = (7/80 : ℝ) := by norm_num [D]
  have e1 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e2 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  have e3 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

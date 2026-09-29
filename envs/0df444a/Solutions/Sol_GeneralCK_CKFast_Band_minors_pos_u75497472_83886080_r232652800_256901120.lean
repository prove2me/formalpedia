-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u75497472_83886080_r232652800_256901120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:53:58.912101+00:00
-- url     : https://prove2.me/submissions/1b8134c1-f9f8-4077-8107-7d8954292c33

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/100, 1/10]`, `ρ ∈ [71/256, 49/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 75497472 77594624 232652800 238714880 ⟨⟨209347528451, 209347528464⟩, ⟨197809841023, 221234649572⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 75497472 77594624 238714880 244776960 ⟨⟨213462828303, 213462828317⟩, ⟨201913644576, 225356464434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 77594624 79691776 232652800 238714880 ⟨⟨206179810335, 206179810344⟩, ⟨194828088433, 217872822911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 77594624 79691776 238714880 244776960 ⟨⟨210262600331, 210262600337⟩, ⟨198897717712, 221964072066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 75497472 77594624 244776960 250839040 ⟨⟨217538584616, 217538584627⟩, ⟨205978634335, 229438078592⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 75497472 77594624 250839040 256901120 ⟨⟨221575884580, 221575884591⟩, ⟨210005858664, 233480616770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 77594624 79691776 244776960 250839040 ⟨⟨214306961212, 214306961215⟩, ⟨202929645073, 226016229883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 77594624 79691776 250839040 256901120 ⟨⟨218313932052, 218313932058⟩, ⟨206924872326, 230030371622⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 79691776 81788928 232652800 238714880 ⟨⟨203088334730, 203088334743⟩, ⟨191916578751, 214593536452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 79691776 81788928 238714880 244776960 ⟨⟨207138364026, 207138364039⟩, ⟨195951907872, 218653827380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 81788928 83886080 232652800 238714880 ⟨⟨200069900348, 200069900359⟩, ⟨189072399741, 211393285685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 81788928 83886080 238714880 244776960 ⟨⟨204086960372, 204086960383⟩, ⟨193073336042, 215422278342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 79691776 81788928 244776960 250839040 ⟨⟨211151052205, 211151052216⟩, ⟨199950618416, 222676112723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 79691776 81788928 250839040 256901120 ⟨⟨215127392376, 215127392389⟩, ⟨203913667768, 226661420429⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 81788928 83886080 244776960 250839040 ⟨⟨208067740949, 208067740959⟩, ⟨197038708953, 219414327304⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 81788928 83886080 250839040 256901120 ⟨⟨212013191278, 212013191290⟩, ⟨200969433469, 223370415264⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 75497472 83886080 232652800 256901120 t = true :=
  ⟨_, (join_su (m := 79691776) (by decide) (join_sr (m := 244776960) (by decide) (join_su (m := 77594624) (by decide) (join_sr (m := 238714880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 238714880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 77594624) (by decide) (join_sr (m := 250839040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 250839040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 244776960) (by decide) (join_su (m := 81788928) (by decide) (join_sr (m := 238714880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 238714880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 81788928) (by decide) (join_sr (m := 250839040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 250839040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (71/256 : ℝ) (49/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((232652800 : ℤ) : ℝ) / (D : ℝ)) = (71/256 : ℝ) := by norm_num [D]
  have e3 : (((256901120 : ℤ) : ℝ) / (D : ℝ)) = (49/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

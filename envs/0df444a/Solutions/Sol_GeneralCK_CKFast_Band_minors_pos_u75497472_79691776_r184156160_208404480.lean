-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u75497472_79691776_r184156160_208404480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:51:31.32492+00:00
-- url     : https://prove2.me/submissions/5fe1c269-62d6-4f96-90ed-5914471ca04c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/100, 19/200]`, `ρ ∈ [281/1280, 159/640]` by 10 cells of the computing
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
theorem cell0 : cellOK 75497472 76546048 184156160 190218240 ⟨⟨175584398234, 175584398245⟩, ⟨167843593430, 183500353446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 76546048 77594624 184156160 190218240 ⟨⟨174134106708, 174134106719⟩, ⟨166465316364, 181975504830⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 75497472 77594624 190218240 196280320 ⟨⟨179332838182, 179332838195⟩, ⟨167899835388, 191152283186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 77594624 78643200 184156160 190218240 ⟨⟨172703754587, 172703754597⟩, ⟨165105690828, 180471939683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 78643200 79691776 184156160 190218240 ⟨⟨171292872329, 171292872340⟩, ⟨163764281970, 178989152126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 77594624 79691776 190218240 196280320 ⟨⟨176428515051, 176428515056⟩, ⟨165192890752, 188040247009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 75497472 77594624 196280320 202342400 ⟨⟨183759059715, 183759059725⟩, ⟨172308154418, 195590882451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 75497472 77594624 202342400 208404480 ⟨⟨188136870241, 188136870254⟩, ⟨176669136736, 199980077673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 77594624 79691776 196280320 202342400 ⟨⟨180812841736, 180812841744⟩, ⟨169557726615, 192438879577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 77594624 79691776 202342400 208404480 ⟨⟨185150290220, 185150290228⟩, ⟨173876740027, 196789650097⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 75497472 79691776 184156160 208404480 t = true :=
  ⟨_, (join_sr (m := 196280320) (by decide) (join_su (m := 77594624) (by decide) (join_sr (m := 190218240) (by decide) (join_su (m := 76546048) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 190218240) (by decide) (join_su (m := 78643200) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (leaf_ok cell5))) (join_su (m := 77594624) (by decide) (join_sr (m := 202342400) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 202342400) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (19/200 : ℝ) →
    rho ∈ Set.Icc (281/1280 : ℝ) (159/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e1 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e2 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  have e3 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

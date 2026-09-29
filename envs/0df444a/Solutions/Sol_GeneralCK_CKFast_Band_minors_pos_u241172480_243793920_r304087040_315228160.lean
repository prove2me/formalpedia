-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_243793920_r304087040_315228160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:39:43.729141+00:00
-- url     : https://prove2.me/submissions/a04b0383-5d7a-412e-9fa2-8205dcb4c0fe

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 93/320]`, `ρ ∈ [29/80, 481/1280]` by 9 cells of the computing
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
theorem cell0 : cellOK 241172480 242483200 304087040 306872320 ⟨⟨93004101293, 93004101301⟩, ⟨89833177081, 96211151766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241172480 242483200 306872320 309657600 ⟨⟨93814658020, 93814658027⟩, ⟨90636964226, 97028515777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 242483200 243138560 304087040 306872320 ⟨⟨92387932812, 92387932819⟩, ⟨90552236371, 94236136718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 243138560 243793920 304087040 306872320 ⟨⟨91978244955, 91978244962⟩, ⟨90147099885, 93821856207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 242483200 243793920 306872320 309657600 ⟨⟨92986999444, 92986999452⟩, ⟨89822378259, 96187590831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 241172480 242483200 309657600 312442880 ⟨⟨94624652728, 94624652735⟩, ⟨91440191353, 97845315599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 241172480 242483200 312442880 315228160 ⟨⟨95434088177, 95434088184⟩, ⟨92242861205, 98661554010⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 242483200 243793920 309657600 312442880 ⟨⟨93790470256, 93790470263⟩, ⟨90619107696, 96997841209⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 242483200 243793920 312442880 315228160 ⟨⟨94593395376, 94593395383⟩, ⟨91415293244, 97807543922⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 243793920 304087040 315228160 t = true :=
  ⟨_, (join_sr (m := 309657600) (by decide) (join_su (m := 242483200) (by decide) (join_sr (m := 306872320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 306872320) (by decide) (join_su (m := 243138560) (by decide) (leaf_ok cell2) (leaf_ok cell3)) (leaf_ok cell4))) (join_su (m := 242483200) (by decide) (join_sr (m := 312442880) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 312442880) (by decide) (leaf_ok cell7) (leaf_ok cell8))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (29/80 : ℝ) (481/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  have e3 : (((315228160 : ℤ) : ℝ) / (D : ℝ)) = (481/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

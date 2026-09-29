-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_217579520_r237240320_248381440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:17:34.121831+00:00
-- url     : https://prove2.me/submissions/d2960c09-6127-412a-8eb8-1f40c0344ae2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 83/320]`, `ρ ∈ [181/640, 379/1280]` by 13 cells of the computing
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
theorem cell0 : cellOK 214958080 215613440 237240320 240025600 ⟨⟨87480095409, 87480095416⟩, ⟨85531055373, 89443534611⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 215613440 216268800 237240320 240025600 ⟨⟨87113024626, 87113024633⟩, ⟨85169212786, 89071178981⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 214958080 215613440 240025600 242810880 ⟨⟨88448927141, 88448927148⟩, ⟨86495852112, 90416404461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 215613440 216268800 240025600 242810880 ⟨⟨88078194865, 88078194871⟩, ⟨86130356703, 90040378868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 216268800 216924160 237240320 240025600 ⟨⟨86746994912, 86746994920⟩, ⟨84808386978, 88699889059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 216924160 217579520 237240320 240025600 ⟨⟨86381998742, 86381998749⟩, ⟨84448570608, 88329657139⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 216268800 216924160 240025600 242810880 ⟨⟨87708509412, 87708509418⟩, ⟨85765883853, 89665424714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 216924160 217579520 240025600 242810880 ⟨⟨87339863237, 87339863244⟩, ⟨85402426198, 89291534266⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 216268800 242810880 245596160 ⟨⟨89229411702, 89229411708⟩, ⟨85934206112, 92564586642⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 214958080 216268800 245596160 248381440 ⟨⟨90194380950, 90194380956⟩, ⟨86891762569, 93536994939⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 216268800 216924160 242810880 245596160 ⟨⟨88669022982, 88669022987⟩, ⟨86722384979, 90629954172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 216924160 217579520 242810880 245596160 ⟨⟨88296738205, 88296738212⟩, ⟨86355297344, 90252416702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 216268800 217579520 245596160 248381440 ⟨⟨89440454107, 89440454113⟩, ⟨86152813330, 92767827388⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 217579520 237240320 248381440 t = true :=
  ⟨_, (join_sr (m := 242810880) (by decide) (join_su (m := 216268800) (by decide) (join_sr (m := 240025600) (by decide) (join_su (m := 215613440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 215613440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 240025600) (by decide) (join_su (m := 216924160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 216924160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 216268800) (by decide) (join_sr (m := 245596160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 245596160) (by decide) (join_su (m := 216924160) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (83/320 : ℝ) →
    rho ∈ Set.Icc (181/640 : ℝ) (379/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e2 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e3 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

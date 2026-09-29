-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u217579520_220200960_r237240320_248381440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:18:04.246157+00:00
-- url     : https://prove2.me/submissions/65f61e00-f8cc-4251-8643-3c7bcffa411d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [83/320, 21/80]`, `ρ ∈ [181/640, 379/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 217579520 218234880 237240320 240025600 ⟨⟨86018028656, 86018028659⟩, ⟨84089756391, 87960475577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 218234880 218890240 237240320 240025600 ⟨⟨85655077250, 85655077257⟩, ⟨83731937107, 87592336789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 217579520 218234880 240025600 242810880 ⟨⟨86972248854, 86972248858⟩, ⟨85039976429, 88918699857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 218234880 218890240 240025600 242810880 ⟨⟨86605658835, 86605658841⟩, ⟨84678527301, 88546913883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 218890240 219545600 237240320 240025600 ⟨⟨85293137190, 85293137197⟩, ⟨83375105595, 87225233262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 219545600 220200960 237240320 240025600 ⟨⟨84932201196, 84932201203⟩, ⟨83019254749, 86859157537⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 218890240 219545600 240025600 242810880 ⟨⟨86240085823, 86240085828⟩, ⟨84318071627, 88176168802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 219545600 220200960 240025600 242810880 ⟨⟨85875522512, 85875522519⟩, ⟨83958602276, 87806457135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 217579520 218234880 242810880 245596160 ⟨⟨87925490824, 87925490827⟩, ⟨85989223223, 89875940846⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 218234880 218890240 242810880 245596160 ⟨⟨87555273385, 87555273393⟩, ⟨85624155345, 89500518976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 218234880 245596160 248381440 ⟨⟨88877759757, 88877759758⟩, ⟨86937501932, 90832203762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 218234880 218890240 245596160 248381440 ⟨⟨88503926017, 88503926022⟩, ⟨86568826325, 90453157213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 218890240 219545600 242810880 245596160 ⟨⟨87186078510, 87186078516⟩, ⟨85260086500, 89126143529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 219545600 220200960 242810880 245596160 ⟨⟨86817898869, 86817898876⟩, ⟨84897009535, 88752807004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 218890240 219545600 245596160 248381440 ⟨⟨88131120293, 88131120298⟩, ⟨86201155228, 90075162513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 219545600 220200960 245596160 248381440 ⟨⟨87759335234, 87759335240⟩, ⟨85834481466, 89698212138⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 217579520 220200960 237240320 248381440 t = true :=
  ⟨_, (join_sr (m := 242810880) (by decide) (join_su (m := 218890240) (by decide) (join_sr (m := 240025600) (by decide) (join_su (m := 218234880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 218234880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 240025600) (by decide) (join_su (m := 219545600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 219545600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 218890240) (by decide) (join_sr (m := 245596160) (by decide) (join_su (m := 218234880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 218234880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 245596160) (by decide) (join_su (m := 219545600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 219545600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (83/320 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (181/640 : ℝ) (379/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e3 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

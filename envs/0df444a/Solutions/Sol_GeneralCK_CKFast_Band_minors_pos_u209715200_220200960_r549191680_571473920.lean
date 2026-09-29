-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_220200960_r549191680_571473920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:48:47.195349+00:00
-- url     : https://prove2.me/submissions/360416f3-4c6a-4a5f-bd9a-04b141eac460

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 21/80]`, `ρ ∈ [419/640, 109/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 212336640 549191680 554762240 ⟨⟨195897052937, 195897052945⟩, ⟨187666068673, 204294886659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 209715200 212336640 554762240 560332800 ⟨⟨197698258011, 197698258019⟩, ⟨189439988200, 206123307201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212336640 214958080 549191680 554762240 ⟨⟨192986377710, 192986377719⟩, ⟨184822646904, 201315917889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212336640 214958080 554762240 560332800 ⟨⟨194765666671, 194765666680⟩, ⟨186574669116, 203122427726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 209715200 212336640 560332800 565903360 ⟨⟨199497200108, 199497200115⟩, ⟨191211676525, 207949428347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209715200 212336640 565903360 571473920 ⟨⟨201293908928, 201293908936⟩, ⟨192981162818, 209773280314⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212336640 214958080 560332800 565903360 ⟨⟨196542778824, 196542778833⟩, ⟨188324543761, 204926726971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 212336640 214958080 565903360 571473920 ⟨⟨198317742546, 198317742555⟩, ⟨190072298717, 206728844483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 217579520 549191680 554762240 ⟨⟨190095357411, 190095357415⟩, ⟨181998065265, 198357425021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 214958080 217579520 554762240 560332800 ⟨⟨191852676584, 191852676588⟩, ⟨183728145855, 200141960321⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 220200960 549191680 554762240 ⟨⟨187223541823, 187223541831⟩, ⟨179191890332, 195418941190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 217579520 220200960 554762240 560332800 ⟨⟨188958840234, 188958840243⟩, ⟨180899987373, 197181441159⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 214958080 217579520 560332800 565903360 ⟨⟨193607902894, 193607902898⟩, ⟨185456160335, 201924371561⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 214958080 217579520 565903360 571473920 ⟨⟨195361063436, 195361063441⟩, ⟨187182135339, 203704686289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 217579520 220200960 560332800 565903360 ⟨⟨190692127521, 190692127529⟩, ⟨182606097609, 198941901349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 217579520 220200960 565903360 571473920 ⟨⟨192423429548, 192423429556⟩, ⟨184310246474, 200700348044⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 220200960 549191680 571473920 t = true :=
  ⟨_, (join_su (m := 214958080) (by decide) (join_sr (m := 560332800) (by decide) (join_su (m := 212336640) (by decide) (join_sr (m := 554762240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 554762240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 212336640) (by decide) (join_sr (m := 565903360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 565903360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 560332800) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 554762240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 554762240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 217579520) (by decide) (join_sr (m := 565903360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 565903360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (419/640 : ℝ) (109/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((549191680 : ℤ) : ℝ) / (D : ℝ)) = (419/640 : ℝ) := by norm_num [D]
  have e3 : (((571473920 : ℤ) : ℝ) / (D : ℝ)) = (109/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

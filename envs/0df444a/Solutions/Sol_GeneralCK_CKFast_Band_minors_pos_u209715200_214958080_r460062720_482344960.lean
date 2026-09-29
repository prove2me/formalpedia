-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_214958080_r460062720_482344960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:30:34.208256+00:00
-- url     : https://prove2.me/submissions/d387103e-284e-4445-ad73-c86ec915e314

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 41/160]`, `ρ ∈ [351/640, 23/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 211025920 460062720 465633280 ⟨⟨167384925294, 167384925303⟩, ⟨162795277880, 172033287439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 211025920 212336640 460062720 465633280 ⟨⟨166106218203, 166106218212⟩, ⟨161539663071, 170731175826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 209715200 211025920 465633280 471203840 ⟨⟨169232427255, 169232427263⟩, ⟨164627940101, 173895585613⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 211025920 212336640 465633280 471203840 ⟨⟨167941979483, 167941979492⟩, ⟨163360599746, 172581722530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 212336640 213647360 460062720 465633280 ⟨⟨164832646716, 164832646718⟩, ⟨160289021260, 169434364496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 213647360 214958080 460062720 465633280 ⟨⟨163564148119, 163564148127⟩, ⟨159043291609, 168142788861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212336640 213647360 465633280 471203840 ⟨⟨166656664211, 166656664214⟩, ⟨162098230661, 171273155162⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 213647360 214958080 465633280 471203840 ⟨⟨165376419001, 165376419010⟩, ⟨160840772252, 169969819229⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 209715200 211025920 471203840 476774400 ⟨⟨171077132575, 171077132582⟩, ⟨166457834262, 175755057219⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 211025920 212336640 471203840 476774400 ⟨⟨169774999657, 169774999666⟩, ⟨165178822944, 174429499169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 209715200 211025920 476774400 482344960 ⟨⟨172919075097, 172919075106⟩, ⟨168284993798, 177611736513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 211025920 212336640 476774400 482344960 ⟨⟨171605311763, 171605311770⟩, ⟨166994365307, 176274539173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 212336640 213647360 471203840 476774400 ⟨⟨168477995347, 168477995351⟩, ⟨163904780391, 173109231465⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 213647360 214958080 471203840 476774400 ⟨⟨167186057488, 167186057495⟩, ⟨162635646259, 171794190141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 212336640 213647360 476774400 482344960 ⟨⟨170296672367, 170296672371⟩, ⟨165708702313, 174942626027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 213647360 214958080 476774400 482344960 ⟨⟨168993095044, 168993095052⟩, ⟨164427944728, 173615933427⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 214958080 460062720 482344960 t = true :=
  ⟨_, (join_sr (m := 471203840) (by decide) (join_su (m := 212336640) (by decide) (join_sr (m := 465633280) (by decide) (join_su (m := 211025920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 211025920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 465633280) (by decide) (join_su (m := 213647360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 213647360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 212336640) (by decide) (join_sr (m := 476774400) (by decide) (join_su (m := 211025920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 211025920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 476774400) (by decide) (join_su (m := 213647360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 213647360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (351/640 : ℝ) (23/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  have e3 : (((482344960 : ℤ) : ℝ) / (D : ℝ)) = (23/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_214958080_r437780480_460062720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:29:33.462977+00:00
-- url     : https://prove2.me/submissions/1b4f063d-7eec-4b12-9378-a1b57510d7c5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 41/160]`, `ρ ∈ [167/320, 351/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 211025920 437780480 443351040 ⟨⟨159966264610, 159966264617⟩, ⟨155436270254, 164555134379⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 211025920 212336640 437780480 443351040 ⟨⟨158735092141, 158735092150⟩, ⟨154228119716, 163300610490⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 209715200 211025920 443351040 448921600 ⟨⟨161825297041, 161825297050⟩, ⟨157280344467, 166429086872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 211025920 212336640 443351040 448921600 ⟨⟨160582153455, 160582153463⟩, ⟨156060241899, 165162577067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 212336640 213647360 437780480 443351040 ⟨⟨157509059451, 157509059455⟩, ⟨153024940971, 162051396795⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 213647360 214958080 437780480 443351040 ⟨⟨156288102801, 156288102810⟩, ⟨151826672281, 160807427555⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212336640 213647360 443351040 448921600 ⟨⟨159344149872, 159344149875⟩, ⟨154845112677, 163901376267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 213647360 214958080 443351040 448921600 ⟨⟨158111222801, 158111222810⟩, ⟨153634895276, 162645419009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 209715200 211025920 448921600 454492160 ⟨⟨163681394714, 163681394722⟩, ⟨159121514173, 168300073013⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 211025920 212336640 448921600 454492160 ⟨⟨162426338882, 162426338890⟩, ⟨157889517437, 167021637191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 209715200 211025920 454492160 460062720 ⟨⟨165534592577, 165534592584⟩, ⟨160959813895, 170168128174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 211025920 212336640 454492160 460062720 ⟨⟨164267682523, 164267682530⟩, ⟨159715980021, 168877825366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 212336640 213647360 448921600 454492160 ⟨⟨161176422421, 161176422425⟩, ⟨156662494755, 165748508313⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 213647360 214958080 448921600 454492160 ⟨⟨159931582095, 159931582102⟩, ⟨155440384821, 164480621201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 212336640 213647360 454492160 460062720 ⟨⟨163005910368, 163005910372⟩, ⟨158477120078, 167592826590⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 213647360 214958080 454492160 460062720 ⟨⟨161749213134, 161749213142⟩, ⟨157243172990, 166313066959⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 214958080 437780480 460062720 t = true :=
  ⟨_, (join_sr (m := 448921600) (by decide) (join_su (m := 212336640) (by decide) (join_sr (m := 443351040) (by decide) (join_su (m := 211025920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 211025920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 443351040) (by decide) (join_su (m := 213647360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 213647360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 212336640) (by decide) (join_sr (m := 454492160) (by decide) (join_su (m := 211025920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 211025920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 454492160) (by decide) (join_su (m := 213647360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 213647360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (167/320 : ℝ) (351/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  have e3 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

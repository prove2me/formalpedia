-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_220200960_r437780480_460062720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:29:49.746277+00:00
-- url     : https://prove2.me/submissions/050e45e7-0b66-44de-9627-eab9751fc91e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 21/80]`, `ρ ∈ [167/320, 351/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 214958080 216268800 437780480 443351040 ⟨⟨155072159333, 155072159341⟩, ⟨150633252729, 159568637930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 216268800 217579520 437780480 443351040 ⟨⟨153861167015, 153861167024⟩, ⟨149444622209, 158334963949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 214958080 216268800 443351040 448921600 ⟨⟨156883309618, 156883309627⟩, ⟨152429528980, 161394640724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 216268800 217579520 443351040 448921600 ⟨⟨155660348522, 155660348530⟩, ⟨151228953890, 160148977696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 217579520 218890240 437780480 443351040 ⟨⟨152655064653, 152655064661⟩, ⟨148260721423, 157106342498⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 218890240 220200960 437780480 443351040 ⟨⟨151453791859, 151453791863⟩, ⟨147081491844, 155882711304⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 217579520 218890240 443351040 448921600 ⟨⟨154442278535, 154442278543⟩, ⟨150033110891, 158908367065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 218890240 220200960 443351040 448921600 ⟨⟨153229039483, 153229039487⟩, ⟨148841941645, 157672746797⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 216268800 448921600 454492160 ⟨⟨158691755520, 158691755527⟩, ⟨154223127136, 163217911561⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 216268800 217579520 448921600 454492160 ⟨⟨157456881131, 157456881139⟩, ⟨153010662001, 161960315948⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 214958080 216268800 454492160 460062720 ⟨⟨160497528690, 160497528698⟩, ⟨156014078481, 165038482463⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 216268800 217579520 454492160 460062720 ⟨⟨159250795715, 159250795723⟩, ⟨154789777066, 163769009930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 217579520 218890240 448921600 454492160 ⟨⟨156226898180, 156226898188⟩, ⟨151802930507, 160707771758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 218890240 220200960 448921600 454492160 ⟨⟨155001746712, 155001746716⟩, ⟨150599874503, 159460217206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 217579520 218890240 454492160 460062720 ⟨⟨158008953696, 158008953704⟩, ⟨153570210038, 162504587022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 218890240 220200960 454492160 460062720 ⟨⟨156771942905, 156771942909⟩, ⟨152355319451, 161245152216⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 220200960 437780480 460062720 t = true :=
  ⟨_, (join_sr (m := 448921600) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 443351040) (by decide) (join_su (m := 216268800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 216268800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 443351040) (by decide) (join_su (m := 218890240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 218890240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 217579520) (by decide) (join_sr (m := 454492160) (by decide) (join_su (m := 216268800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 216268800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 454492160) (by decide) (join_su (m := 218890240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 218890240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (167/320 : ℝ) (351/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  have e3 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_115343360_r508559360_555745280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:45:53.57037+00:00
-- url     : https://prove2.me/submissions/ff3fb6e8-8d8f-472f-87e7-57bc1568668b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 11/80]`, `ρ ∈ [97/160, 53/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 107479040 508559360 520355840 ⟨⟨317980245800, 317980245812⟩, ⟨303268623999, 333037876233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 107479040 110100480 508559360 520355840 ⟨⟨313818945531, 313818945542⟩, ⟨299283784405, 328697433719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 104857600 107479040 520355840 532152320 ⟨⟨323549412025, 323549412038⟩, ⟨308810156025, 338627120369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 107479040 110100480 520355840 532152320 ⟨⟨319353624739, 319353624752⟩, ⟨304788405453, 334254933526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 110100480 112721920 508559360 520355840 ⟨⟨309715074062, 309715074066⟩, ⟨295353039961, 324417724733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 112721920 115343360 508559360 520355840 ⟨⟨305666850414, 305666850424⟩, ⟨291474714026, 320196868780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 110100480 112721920 520355840 532152320 ⟨⟨315214489363, 315214489369⟩, ⟨300820101546, 329942564435⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 112721920 115343360 520355840 532152320 ⟨⟨311130265331, 311130265343⟩, ⟨296903602437, 325688178977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 104857600 107479040 532152320 543948800 ⟨⟨329080843874, 329080843887⟩, ⟨314314582888, 344178077218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 107479040 110100480 532152320 543948800 ⟨⟨324851445808, 324851445820⟩, ⟨310256813249, 339774997443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 104857600 107479040 543948800 555745280 ⟨⟨334575983591, 334575983604⟩, ⟨319783303908, 349692228902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 107479040 110100480 543948800 555745280 ⟨⟨330313802755, 330313802767⟩, ⟨315690359695, 345259058930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 110100480 112721920 532152320 543948800 ⟨⟨320677917973, 320677917981⟩, ⟨306251833639, 335430818882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 112721920 115343360 532152320 543948800 ⟨⟨316558559223, 316558559236⟩, ⟨302298036239, 331143752474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 110100480 112721920 543948800 555745280 ⟨⟨326106706838, 326106706846⟩, ⟨311649541951, 340883873898⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 112721920 115343360 543948800 555745280 ⟨⟨321953033114, 321953033127⟩, ⟨307659276174, 336564928511⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 115343360 508559360 555745280 t = true :=
  ⟨_, (join_sr (m := 532152320) (by decide) (join_su (m := 110100480) (by decide) (join_sr (m := 520355840) (by decide) (join_su (m := 107479040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 107479040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 520355840) (by decide) (join_su (m := 112721920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 112721920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 110100480) (by decide) (join_sr (m := 543948800) (by decide) (join_su (m := 107479040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 107479040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 543948800) (by decide) (join_su (m := 112721920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 112721920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (97/160 : ℝ) (53/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((508559360 : ℤ) : ℝ) / (D : ℝ)) = (97/160 : ℝ) := by norm_num [D]
  have e3 : (((555745280 : ℤ) : ℝ) / (D : ℝ)) = (53/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

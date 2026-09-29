-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_125829120_r650117120_697303040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:52:01.535067+00:00
-- url     : https://prove2.me/submissions/fec8883b-6cfc-4948-8409-1705b938f884

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 3/20]`, `ρ ∈ [31/40, 133/160]` by 18 cells of the computing
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
theorem cell0 : cellOK 104857600 110100480 650117120 661913600 ⟨⟨380344675143, 380344675156⟩, ⟨356093433733, 405298923039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 104857600 110100480 661913600 673710080 ⟨⟨385533116593, 385533116606⟩, ⟨361221922072, 410530495846⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 110100480 115343360 650117120 661913600 ⟨⟨371386761573, 371386761586⟩, ⟨347565587507, 395915339955⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 110100480 115343360 661913600 673710080 ⟨⟨376520317525, 376520317537⟩, ⟨352632890208, 401099474273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 104857600 110100480 673710080 685506560 ⟨⟨390698538496, 390698538509⟩, ⟨366327917898, 415738565859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 104857600 110100480 685506560 697303040 ⟨⟨395841909973, 395841909984⟩, ⟨371412353266, 420924133642⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 110100480 115343360 673710080 685506560 ⟨⟨381631729764, 381631729776⟩, ⟨357678614268, 406260919072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 110100480 115343360 685506560 697303040 ⟨⟨386721915352, 386721915363⟩, ⟨362703640269, 411400623203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 115343360 120586240 650117120 661913600 ⟨⟨362612816534, 362612816540⟩, ⟨339209601497, 386726733599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 115343360 120586240 661913600 673710080 ⟨⟨367688545678, 367688545684⟩, ⟨344213308504, 391859911242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 120586240 123207680 650117120 661913600 ⟨⟨356147045669, 356147045683⟩, ⟨341999263713, 370556558654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 123207680 125829120 650117120 661913600 ⟨⟨351888944818, 351888944826⟩, ⟨337878452354, 366161159791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 120586240 123207680 661913600 673710080 ⟨⟨361177604256, 361177604268⟩, ⟨346995495598, 375615918877⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 123207680 125829120 661913600 673710080 ⟨⟨356888579406, 356888579414⟩, ⟨342842073654, 371191485002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 115343360 120586240 673710080 685506560 ⟨⟨372743016333, 372743016341⟩, ⟨349196347859, 396971237315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 115343360 120586240 685506560 697303040 ⟨⟨377777094881, 377777094886⟩, ⟨354159550395, 402061609856⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 120586240 125829120 673710080 685506560 ⟨⟨364022829624, 364022829637⟩, ⟨340872160820, 387859464799⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 120586240 125829120 685506560 697303040 ⟨⟨368998083575, 368998083585⟩, ⟨345771298662, 392897272506⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 125829120 650117120 697303040 t = true :=
  ⟨_, (join_su (m := 115343360) (by decide) (join_sr (m := 673710080) (by decide) (join_su (m := 110100480) (by decide) (join_sr (m := 661913600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 661913600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 110100480) (by decide) (join_sr (m := 685506560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 685506560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 673710080) (by decide) (join_su (m := 120586240) (by decide) (join_sr (m := 661913600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 661913600) (by decide) (join_su (m := 123207680) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_su (m := 123207680) (by decide) (leaf_ok cell12) (leaf_ok cell13)))) (join_su (m := 120586240) (by decide) (join_sr (m := 685506560) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_sr (m := 685506560) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (31/40 : ℝ) (133/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((650117120 : ℤ) : ℝ) / (D : ℝ)) = (31/40 : ℝ) := by norm_num [D]
  have e3 : (((697303040 : ℤ) : ℝ) / (D : ℝ)) = (133/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

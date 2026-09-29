-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_125829120_r697303040_744488960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:51:57.071996+00:00
-- url     : https://prove2.me/submissions/ad6b3f9b-5df9-4f53-9ee0-ce82859586b1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 3/20]`, `ρ ∈ [133/160, 71/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 110100480 697303040 709099520 ⟨⟨400964173593, 400964173606⟩, ⟨376476135291, 426088171564⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 104857600 110100480 709099520 720896000 ⟨⟨406066246658, 406066246673⟩, ⟨381520147334, 431231625172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 110100480 115343360 697303040 709099520 ⟨⟨391791767077, 391791767090⟩, ⟨367708826031, 416519509694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 110100480 115343360 709099520 720896000 ⟨⟨396842154607, 396842154620⟩, ⟨372695007657, 421618476981⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 104857600 110100480 720896000 732692480 ⟨⟨411149022421, 411149022434⟩, ⟨386545250123, 436355414523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 104857600 110100480 732692480 744488960 ⟨⟨416213371245, 416213371260⟩, ⟨391552282830, 441460435416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 110100480 115343360 720896000 732692480 ⟨⟨401873925584, 401873925598⟩, ⟨377663000552, 426698400098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 110100480 115343360 732692480 744488960 ⟨⟨406887906665, 406887906677⟩, ⟨382613600372, 431760131792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 115343360 120586240 697303040 709099520 ⟨⟨382791625558, 382791625567⟩, ⟨359103726191, 407131903313⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 115343360 120586240 709099520 720896000 ⟨⟨387787431508, 387787431514⟩, ⟨364029665523, 412182969648⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 120586240 125829120 697303040 709099520 ⟨⟨373954582375, 373954582389⟩, ⟨350652219823, 397915759100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 120586240 125829120 709099520 720896000 ⟨⟨378893103877, 378893103889⟩, ⟨355515670246, 402915730938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 115343360 120586240 720896000 732692480 ⟨⟨392765315729, 392765315735⟩, ⟨368938139758, 417215639400⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 115343360 120586240 732692480 744488960 ⟨⟨397726062035, 397726062043⟩, ⟨373829902216, 422230722689⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 120586240 125829120 720896000 732692480 ⟨⟨383814407567, 383814407580⟩, ⟨360362378640, 407897974816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 120586240 125829120 732692480 744488960 ⟨⟨388719235424, 388719235437⟩, ⟨365193057252, 412863258871⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 125829120 697303040 744488960 t = true :=
  ⟨_, (join_su (m := 115343360) (by decide) (join_sr (m := 720896000) (by decide) (join_su (m := 110100480) (by decide) (join_sr (m := 709099520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 709099520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 110100480) (by decide) (join_sr (m := 732692480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 732692480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 720896000) (by decide) (join_su (m := 120586240) (by decide) (join_sr (m := 709099520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 709099520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 120586240) (by decide) (join_sr (m := 732692480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 732692480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (133/160 : ℝ) (71/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((697303040 : ℤ) : ℝ) / (D : ℝ)) = (133/160 : ℝ) := by norm_num [D]
  have e3 : (((744488960 : ℤ) : ℝ) / (D : ℝ)) = (71/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

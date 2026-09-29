-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_75497472_r402391040_450887680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:57:32.716198+00:00
-- url     : https://prove2.me/submissions/45707c39-5195-4aee-943f-4678a7bf9458

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 9/100]`, `ρ ∈ [307/640, 43/80]` by 10 cells of the computing
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
theorem cell0 : cellOK 67108864 69206016 402391040 414515200 ⟨⟨330022777397, 330022777411⟩, ⟨313907319339, 346546618797⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 69206016 71303168 402391040 414515200 ⟨⟨325961162420, 325961162434⟩, ⟨310060866520, 342265096358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 67108864 71303168 414515200 426639360 ⟨⟨334671386406, 334671386420⟩, ⟨310532378011, 359740029550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 71303168 73400320 402391040 414515200 ⟨⟨321972981500, 321972981514⟩, ⟨306282800965, 338062075348⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 73400320 75497472 402391040 414515200 ⟨⟨318055608799, 318055608814⟩, ⟨302570691378, 333934740592⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 71303168 75497472 414515200 426639360 ⟨⟨326647604504, 326647604518⟩, ⟨303095610192, 351111386518⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 67108864 71303168 426639360 438763520 ⟨⟨341280583689, 341280583703⟩, ⟨317154808672, 366305853778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 67108864 71303168 438763520 450887680 ⟨⟨347813993703, 347813993715⟩, ⟨323702147040, 372795980325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 71303168 75497472 426639360 438763520 ⟨⟨333212675424, 333212675436⟩, ⟨309661506042, 357647714756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 71303168 75497472 438763520 450887680 ⟨⟨339704388531, 339704388545⟩, ⟨316154989824, 364110410868⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 75497472 402391040 450887680 t = true :=
  ⟨_, (join_sr (m := 426639360) (by decide) (join_su (m := 71303168) (by decide) (join_sr (m := 414515200) (by decide) (join_su (m := 69206016) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 414515200) (by decide) (join_su (m := 73400320) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (leaf_ok cell5))) (join_su (m := 71303168) (by decide) (join_sr (m := 438763520) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 438763520) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (9/100 : ℝ) →
    rho ∈ Set.Icc (307/640 : ℝ) (43/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e2 : (((402391040 : ℤ) : ℝ) / (D : ℝ)) = (307/640 : ℝ) := by norm_num [D]
  have e3 : (((450887680 : ℤ) : ℝ) / (D : ℝ)) = (43/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

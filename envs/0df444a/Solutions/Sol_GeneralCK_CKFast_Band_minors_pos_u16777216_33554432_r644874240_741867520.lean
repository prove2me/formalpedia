-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_33554432_r644874240_741867520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:34:00.94795+00:00
-- url     : https://prove2.me/submissions/6811424b-3d96-412c-8e2c-689b2001e90c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 1/25]`, `ρ ∈ [123/160, 283/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 16777216 20971520 644874240 669122560 ⟨⟨578103405102, 578103405119⟩, ⟨539049940360, 617255205318⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 20971520 25165824 644874240 669122560 ⟨⟨565385836719, 565385836736⟩, ⟨527281113404, 603710946408⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 16777216 20971520 669122560 693370880 ⟨⟨588964931539, 588964931556⟩, ⟨550417995128, 627505621064⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 20971520 25165824 669122560 693370880 ⟨⟨576360811125, 576360811144⟩, ⟨538710676031, 614129277136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 25165824 29360128 644874240 669122560 ⟨⟨553273177360, 553273177377⟩, ⟨516033875504, 590826578282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 29360128 33554432 644874240 669122560 ⟨⟨541676029061, 541676029077⟩, ⟨505240921103, 578500525762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 25165824 29360128 669122560 693370880 ⟨⟨564340339658, 564340339675⟩, ⟨527508043274, 601387451373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 29360128 33554432 669122560 693370880 ⟨⟨552816768648, 552816768663⟩, ⟨516744764694, 589181805510⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 16777216 20971520 693370880 717619200 ⟨⟨599732489775, 599732489790⟩, ⟨561665362310, 637695141197⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 20971520 25165824 693370880 717619200 ⟨⟨587235520068, 587235520084⟩, ⟨550016675393, 624476566747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 16777216 20971520 717619200 741867520 ⟨⟨610418210345, 610418210362⟩, ⟨572806137442, 647833092542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 20971520 25165824 717619200 741867520 ⟨⟨598022458881, 598022458900⟩, ⟨561213216343, 634762935522⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 25165824 29360128 693370880 717619200 ⟨⟨575302246089, 575302246107⟩, ⟨538856689359, 611868843825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 29360128 33554432 693370880 717619200 ⟨⟨563848371453, 563848371468⟩, ⟨528121904711, 599776620060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 25165824 29360128 717619200 741867520 ⟨⟨586171620460, 586171620475⟩, ⟨550093842615, 622281477408⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 29360128 33554432 717619200 741867520 ⟨⟨574783678063, 574783678078⟩, ⟨539386225236, 610296133489⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 33554432 644874240 741867520 t = true :=
  ⟨_, (join_sr (m := 693370880) (by decide) (join_su (m := 25165824) (by decide) (join_sr (m := 669122560) (by decide) (join_su (m := 20971520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 20971520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 669122560) (by decide) (join_su (m := 29360128) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 29360128) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 25165824) (by decide) (join_sr (m := 717619200) (by decide) (join_su (m := 20971520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 20971520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 717619200) (by decide) (join_su (m := 29360128) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 29360128) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (123/160 : ℝ) (283/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((644874240 : ℤ) : ℝ) / (D : ℝ)) = (123/160 : ℝ) := by norm_num [D]
  have e3 : (((741867520 : ℤ) : ℝ) / (D : ℝ)) = (283/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

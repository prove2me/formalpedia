-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_50331648_r741867520_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:57:01.339106+00:00
-- url     : https://prove2.me/submissions/8c29f862-f9c2-4617-92bd-1c9a1bdffcaf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 3/50]`, `ρ ∈ [283/320, 1]` by 16 cells of the computing
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
theorem cell0 : cellOK 33554432 37748736 741867520 766115840 ⟨⟨574697309153, 574697309171⟩, ⟨540220517496, 609278491483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 37748736 41943040 741867520 766115840 ⟨⟨564103336032, 564103336047⟩, ⟨530204806030, 598169052559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 33554432 37748736 766115840 790364160 ⟨⟨585520125691, 585520125705⟩, ⟨551309803871, 619757162763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 37748736 41943040 766115840 790364160 ⟨⟨574959700211, 574959700226⟩, ⟨541297318471, 608713490263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 41943040 46137344 741867520 766115840 ⟨⟨553816684312, 553816684327⟩, ⟨520472685526, 587383201187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 46137344 50331648 741867520 766115840 ⟨⟨543808117526, 543808117541⟩, ⟨510998650321, 576889339191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 41943040 46137344 766115840 790364160 ⟨⟨564695662512, 564695662528⟩, ⟨531559293916, 597980750280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 46137344 50331648 766115840 790364160 ⟨⟨554699664944, 554699664959⟩, ⟨522070959386, 587528368678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 33554432 37748736 790364160 814612480 ⟨⟨596276793543, 596276793560⟩, ⟨562320738597, 630184635694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 37748736 41943040 790364160 814612480 ⟨⟨585747709584, 585747709601⟩, ⟨552310762338, 619202836854⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 33554432 37748736 814612480 838860800 ⟨⟨606976853841, 606976853855⟩, ⟨573263477384, 640569453772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 37748736 41943040 814612480 838860800 ⟨⟨596476912932, 596476912947⟩, ⟨563255173546, 629645801041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 41943040 46137344 790364160 814612480 ⟨⟨575504571808, 575504571825⟩, ⟨542566471200, 608519949591⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 46137344 50331648 790364160 814612480 ⟨⟨565519865235, 565519865252⟩, ⟨533063785825, 598106355840⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 41943040 46137344 814612480 838860800 ⟨⟨586252924471, 586252924485⟩, ⟨553504105218, 619009611309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 46137344 50331648 814612480 838860800 ⟨⟨576278156566, 576278156581⟩, ⟨543986845859, 608632163008⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 50331648 741867520 838860800 t = true :=
  ⟨_, (join_sr (m := 790364160) (by decide) (join_su (m := 41943040) (by decide) (join_sr (m := 766115840) (by decide) (join_su (m := 37748736) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 37748736) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 766115840) (by decide) (join_su (m := 46137344) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 46137344) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 41943040) (by decide) (join_sr (m := 814612480) (by decide) (join_su (m := 37748736) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 37748736) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 814612480) (by decide) (join_su (m := 46137344) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 46137344) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (283/320 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((741867520 : ℤ) : ℝ) / (D : ℝ)) = (283/320 : ℝ) := by norm_num [D]
  have e3 : (((838860800 : ℤ) : ℝ) / (D : ℝ)) = (1 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

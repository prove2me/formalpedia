-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u183500800_188743680_r259522560_281804800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:46:48.169971+00:00
-- url     : https://prove2.me/submissions/47073199-fa51-4fb2-8110-39bfb5b1c4e5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/32, 9/40]`, `ρ ∈ [99/320, 43/128]` by 19 cells of the computing
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
theorem cell0 : cellOK 183500800 184811520 259522560 265093120 ⟨⟨115994750083, 115994750091⟩, ⟨111479485904, 120579876577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 184811520 186122240 259522560 262307840 ⟨⟨114512325375, 114512325382⟩, ⟨110780031186, 118291673155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 184811520 186122240 262307840 265093120 ⟨⟨115641068283, 115641068289⟩, ⟨111900866311, 119428316039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 183500800 184811520 265093120 270663680 ⟨⟨118264249604, 118264249611⟩, ⟨113731768488, 122866498292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 184811520 186122240 265093120 270663680 ⟨⟨117331183729, 117331183735⟩, ⟨112825245970, 121906304411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 186122240 187432960 259522560 262307840 ⟨⟨113604400380, 113604400382⟩, ⟨109891201552, 117364306347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 186122240 187432960 262307840 265093120 ⟨⟨114725525691, 114725525695⟩, ⟨111004438339, 118493314246⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 187432960 188743680 259522560 262307840 ⟨⟨112702486506, 112702486513⟩, ⟨109008178473, 116443159854⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 187432960 188743680 262307840 265093120 ⟨⟨113816016583, 113816016590⟩, ⟨110113839769, 117564554590⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 186122240 187432960 265093120 270663680 ⟨⟨116404276176, 116404276178⟩, ⟨111924609448, 120952548822⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 187432960 188743680 265093120 270663680 ⟨⟨115483434584, 115483434591⟩, ⟨111029770954, 120005134644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 183500800 184811520 270663680 276234240 ⟨⟨120527272688, 120527272695⟩, ⟨115977661423, 125146555014⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 184811520 186122240 270663680 276234240 ⟨⟨119579125308, 119579125314⟩, ⟨115056096441, 124171247015⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 183500800 184811520 276234240 281804800 ⟨⟨122783900457, 122783900465⟩, ⟨118217244498, 127420129209⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 184811520 186122240 276234240 281804800 ⟨⟨121820801271, 121820801278⟩, ⟨117280764404, 126429839149⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 186122240 187432960 270663680 276234240 ⟨⟨118637177731, 118637177735⟩, ⟨114140460363, 123202417191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 187432960 188743680 270663680 276234240 ⟨⟨117701337473, 117701337482⟩, ⟨113230665046, 122239968600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 186122240 187432960 276234240 281804800 ⟨⟨120863941162, 120863941166⟩, ⟨116350253954, 125446064903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 187432960 188743680 276234240 281804800 ⟨⟨119913227560, 119913227567⟩, ⟨115425624864, 124468709495⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 183500800 188743680 259522560 281804800 t = true :=
  ⟨_, (join_sr (m := 270663680) (by decide) (join_su (m := 186122240) (by decide) (join_sr (m := 265093120) (by decide) (join_su (m := 184811520) (by decide) (leaf_ok cell0) (join_sr (m := 262307840) (by decide) (leaf_ok cell1) (leaf_ok cell2))) (join_su (m := 184811520) (by decide) (leaf_ok cell3) (leaf_ok cell4))) (join_sr (m := 265093120) (by decide) (join_su (m := 187432960) (by decide) (join_sr (m := 262307840) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 262307840) (by decide) (leaf_ok cell7) (leaf_ok cell8))) (join_su (m := 187432960) (by decide) (leaf_ok cell9) (leaf_ok cell10)))) (join_su (m := 186122240) (by decide) (join_sr (m := 276234240) (by decide) (join_su (m := 184811520) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 184811520) (by decide) (leaf_ok cell13) (leaf_ok cell14))) (join_sr (m := 276234240) (by decide) (join_su (m := 187432960) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_su (m := 187432960) (by decide) (leaf_ok cell17) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/32 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (99/320 : ℝ) (43/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  have e3 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

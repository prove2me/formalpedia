-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u144179200_146800640_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:18:05.910525+00:00
-- url     : https://prove2.me/submissions/0bbf024f-f5cc-42c1-aff6-0d3153c05b50

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/64, 7/40]`, `ρ ∈ [1/10, 137/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 144179200 144834560 83886080 85360640 ⟨⟨52020834418, 52020834425⟩, ⟨50060997275, 53997717001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 144179200 144834560 85360640 86835200 ⟨⟨52881863420, 52881863427⟩, ⟨50918979530, 54861783709⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 144834560 145489920 83886080 85360640 ⟨⟨51781243699, 51781243707⟩, ⟨49828121021, 53751303270⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 144834560 145489920 85360640 86835200 ⟨⟨52638661567, 52638661573⟩, ⟨50682502496, 54611748801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 144179200 144834560 86835200 88309760 ⟨⟨53741480243, 53741480249⟩, ⟨51775560055, 55724427728⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 144179200 144834560 88309760 89784320 ⟨⟨54599691490, 54599691496⟩, ⟨52630745385, 56585655723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 144834560 145489920 86835200 88309760 ⟨⟨53494684009, 53494684017⟩, ⟨51535498831, 55470788558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 144834560 145489920 88309760 89784320 ⟨⟨54349317520, 54349317527⟩, ⟨52387116454, 56328429099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 145489920 146145280 83886080 85360640 ⟨⟨51543099425, 51543099428⟩, ⟨49596637631, 53506390744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 145489920 146145280 85360640 86835200 ⟨⟨52396923849, 52396923852⟩, ⟨50447435990, 54363232808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 146145280 146800640 83886080 85360640 ⟨⟨51306385566, 51306385572⟩, ⟨49366531737, 53262962732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 146145280 146800640 85360640 86835200 ⟨⟨52156634080, 52156634086⟩, ⟨50213764486, 54116218881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 145489920 146145280 86835200 88309760 ⟨⟨53249369396, 53249369399⟩, ⟨51296865597, 55218685807⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 145489920 146145280 88309760 89784320 ⟨⟨54100442446, 54100442449⟩, ⟨52144932766, 56072756184⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 146145280 146800640 86835200 88309760 ⟨⟨53005520056, 53005520064⟩, ⟨51059644664, 54968102466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 146145280 146800640 88309760 89784320 ⟨⟨53853049770, 53853049776⟩, ⟨51904178483, 55818619819⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 144179200 146800640 83886080 89784320 t = true :=
  ⟨_, (join_su (m := 145489920) (by decide) (join_sr (m := 86835200) (by decide) (join_su (m := 144834560) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 85360640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 144834560) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 88309760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 86835200) (by decide) (join_su (m := 146145280) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 85360640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 146145280) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 88309760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/64 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((144179200 : ℤ) : ℝ) / (D : ℝ)) = (11/64 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_196608000_r159252480_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:41:10.631674+00:00
-- url     : https://prove2.me/submissions/58b1643d-2933-4699-9828-0d45bb4bb516

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 15/64]`, `ρ ∈ [243/1280, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 193986560 194641920 159252480 162037760 ⟨⟨68698338350, 68698338356⟩, ⟨66692293322, 70720901850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 194641920 195297280 159252480 162037760 ⟨⟨68408455978, 68408455981⟩, ⟨66408252322, 70425099694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 193986560 194641920 162037760 164823040 ⟨⟨69832115859, 69832115865⟩, ⟨67821486532, 71859261617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 194641920 195297280 162037760 164823040 ⟨⟨69537884589, 69537884591⟩, ⟨67533108673, 71559098820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 195297280 195952640 159252480 162037760 ⟨⟨68119646543, 68119646549⟩, ⟨66125252221, 70130403120⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 195952640 196608000 159252480 162037760 ⟨⟨67831901296, 67831901302⟩, ⟨65843284540, 69836803085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 195297280 195952640 162037760 164823040 ⟨⟨69244737462, 69244737468⟩, ⟨67245782923, 71260052803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 195952640 196608000 162037760 164823040 ⟨⟨68952665663, 68952665669⟩, ⟨66959500739, 70962114457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 194641920 164823040 167608320 ⟨⟨70964168332, 70964168339⟩, ⟨68948966100, 72995884832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 194641920 195297280 164823040 167608320 ⟨⟨70665607636, 70665607639⟩, ⟨68656270671, 72691381058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 193986560 194641920 167608320 170393600 ⟨⟨72094506121, 72094506127⟩, ⟨70074742300, 74130781929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 194641920 195297280 167608320 170393600 ⟨⟨71791635318, 71791635321⟩, ⟨69777748427, 73821956682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 195297280 195952640 164823040 167608320 ⟨⟨70368142095, 70368142103⟩, ⟨68364638365, 72388005062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 195952640 196608000 164823040 167608320 ⟨⟨70071762830, 70071762837⟩, ⟨68074060579, 72085747677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 195297280 195952640 167608320 170393600 ⟨⟨71489870487, 71489870495⟩, ⟨69481828507, 73514270018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 195952640 196608000 167608320 170393600 ⟨⟨71189202688, 71189202695⟩, ⟨69186973871, 73207712707⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 196608000 159252480 170393600 t = true :=
  ⟨_, (join_sr (m := 164823040) (by decide) (join_su (m := 195297280) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 194641920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 194641920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 162037760) (by decide) (join_su (m := 195952640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 195952640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 195297280) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 194641920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 194641920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 167608320) (by decide) (join_su (m := 195952640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 195952640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (15/64 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((196608000 : ℤ) : ℝ) / (D : ℝ)) = (15/64 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

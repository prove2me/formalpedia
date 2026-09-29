-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_237240320_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:36:13.325705+00:00
-- url     : https://prove2.me/submissions/02d40c46-b67b-4cc4-92c0-bd2287ff90fc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 181/640]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 236257280 125829120 127221760 ⟨⟨41248515030, 41248515036⟩, ⟨40426591162, 42073532403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 236257280 236584960 125829120 127221760 ⟨⟨41153876945, 41153876950⟩, ⟨40332983431, 41977857541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 235929600 236257280 127221760 128614400 ⟨⟨41691932060, 41691932066⟩, ⟨40869039967, 42517918998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 236257280 236584960 127221760 128614400 ⟨⟨41596321935, 41596321941⟩, ⟨40774461749, 42421270550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 236584960 236912640 125829120 127221760 ⟨⟨41059377035, 41059377038⟩, ⟨40239511505, 41882323242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 236912640 237240320 125829120 127221760 ⟨⟨40965014766, 40965014771⟩, ⟨40146174861, 41786928970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 236584960 236912640 127221760 128614400 ⟨⟨41500851118, 41500851120⟩, ⟨40680020468, 42324763797⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 236912640 237240320 127221760 128614400 ⟨⟨41405519069, 41405519074⟩, ⟨40585715592, 42228398203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 236257280 128614400 130007040 ⟨⟨42135134990, 42135134996⟩, ⟨41311275086, 42962091077⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 236257280 236584960 128614400 130007040 ⟨⟨42038554203, 42038554208⟩, ⟨41215727753, 42864470424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 235929600 236257280 130007040 131399680 ⟨⟨42578124329, 42578124335⟩, ⟨41753297026, 43406049150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 236257280 236584960 130007040 131399680 ⟨⟨42480574251, 42480574257⟩, ⟨41656781944, 43307457671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 236584960 236912640 128614400 130007040 ⟨⟨41942113846, 41942113848⟩, ⟨41120318478, 42766992593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 236912640 237240320 128614400 130007040 ⟨⟨41845813380, 41845813386⟩, ⟨41025046729, 42669657045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 236584960 236912640 130007040 131399680 ⟨⟨42383165723, 42383165725⟩, ⟨41560406037, 43209010134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 236912640 237240320 130007040 131399680 ⟨⟨42285898197, 42285898203⟩, ⟨41464168766, 43110705995⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 237240320 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 236584960) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 236257280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 236257280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 236912640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 236912640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 236584960) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 236257280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 236257280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 236912640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 236912640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (181/640 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

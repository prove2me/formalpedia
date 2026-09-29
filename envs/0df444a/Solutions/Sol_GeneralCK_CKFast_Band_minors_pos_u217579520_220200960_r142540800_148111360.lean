-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u217579520_220200960_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:23:08.360833+00:00
-- url     : https://prove2.me/submissions/6d9df7e3-b6c6-4592-bc73-852345dc0aef

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [83/320, 21/80]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 217579520 218234880 142540800 143933440 ⟨⟨52705846228, 52705846230⟩, ⟨51202469640, 54218803618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 217579520 218234880 143933440 145326080 ⟨⟨53201518226, 53201518228⟩, ⟨51696228211, 54716393710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 218234880 218890240 142540800 143933440 ⟨⟨52474860725, 52474860730⟩, ⟨50974866297, 53984399817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 218234880 218890240 143933440 145326080 ⟨⟨52968495197, 52968495202⟩, ⟨51466592535, 54479947234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 217579520 218234880 145326080 146718720 ⟨⟨53696896380, 53696896382⟩, ⟨52189694011, 55213688869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 217579520 218234880 146718720 148111360 ⟨⟨54191981462, 54191981464⟩, ⟨52682867807, 55710689871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 218234880 218890240 145326080 146718720 ⟨⟨53461839366, 53461839371⟩, ⟨51958029517, 54975203286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 218234880 218890240 146718720 148111360 ⟨⟨53954893991, 53954893998⟩, ⟨52449178002, 55470168734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 218890240 219545600 142540800 143933440 ⟨⟨52244621691, 52244621698⟩, ⟨50747991566, 53750760597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 218890240 219545600 143933440 145326080 ⟨⟨52736223615, 52736223620⟩, ⟨51237690437, 54244270327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 219545600 220200960 142540800 143933440 ⟨⟨52015123302, 52015123308⟩, ⟨50521839763, 53517879991⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 219545600 220200960 143933440 145326080 ⟨⟨52504697623, 52504697629⟩, ⟨51009516205, 54009356989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 218890240 219545600 145326080 146718720 ⟨⟨53227538740, 53227538745⟩, ⟨51727103535, 54737492221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 218890240 219545600 146718720 148111360 ⟨⟨53718567816, 53718567823⟩, ⟨52216231604, 55230427030⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 219545600 220200960 145326080 146718720 ⟨⟨52993988616, 52993988622⟩, ⟨51496910319, 54500549644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 219545600 220200960 146718720 148111360 ⟨⟨53482997018, 53482997023⟩, ⟨51984022837, 54991458697⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 217579520 220200960 142540800 148111360 t = true :=
  ⟨_, (join_su (m := 218890240) (by decide) (join_sr (m := 145326080) (by decide) (join_su (m := 218234880) (by decide) (join_sr (m := 143933440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 143933440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 218234880) (by decide) (join_sr (m := 146718720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 146718720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 145326080) (by decide) (join_su (m := 219545600) (by decide) (join_sr (m := 143933440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 143933440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 219545600) (by decide) (join_sr (m := 146718720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 146718720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (83/320 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u159907840_161218560_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:16:37.671713+00:00
-- url     : https://prove2.me/submissions/43750380-d14f-441b-affc-4be0e0ac01b9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [61/320, 123/640]`, `ρ ∈ [1/10, 137/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 159907840 160235520 83886080 85360640 ⟨⟨46692164777, 46692164783⟩, ⟨45558315445, 47831845242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 160235520 160563200 83886080 85360640 ⟨⟨46587450671, 46587450678⟩, ⟨45455569261, 47725144779⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 159907840 160235520 85360640 86835200 ⟨⟨47471912364, 47471912372⟩, ⟨46336458910, 48613193812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 160235520 160563200 85360640 86835200 ⟨⟨47365580986, 47365580993⟩, ⟨46232098412, 48504873164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 160563200 160890880 83886080 85360640 ⟨⟨46483018456, 46483018462⟩, ⟨45353098060, 47618733206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 160890880 161218560 83886080 85360640 ⟨⟨46378866684, 46378866690⟩, ⟨45250900435, 47512609035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 160563200 160890880 85360640 86835200 ⟨⟨47259535095, 47259535103⟩, ⟨46128016492, 48396845007⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 160890880 161218560 85360640 86835200 ⟨⟨47153773230, 47153773238⟩, ⟨46024211723, 48289107841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 159907840 160235520 86835200 88309760 ⟨⟨48250594852, 48250594860⟩, ⟨47113542101, 49393472442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 160235520 160563200 86835200 88309760 ⟨⟨48142652486, 48142652492⟩, ⟨47007573535, 49283537931⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 159907840 160235520 88309760 89784320 ⟨⟨49028216647, 49028216655⟩, ⟨47889569394, 50172685566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 160235520 160563200 88309760 89784320 ⟨⟨48918669538, 48918669544⟩, ⟨47781998970, 50061143477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 160563200 160890880 86835200 88309760 ⟨⟨48034999166, 48034999172⟩, ⟨46901887101, 49173899476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 160890880 161218560 86835200 88309760 ⟨⟨47927633417, 47927633423⟩, ⟨46796481362, 49064555560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 160563200 160890880 88309760 89784320 ⟨⟨48809414999, 48809415007⟩, ⟨47674714196, 49949900971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 160890880 161218560 88309760 89784320 ⟨⟨48700451541, 48700451547⟩, ⟨47567713621, 49838956518⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 159907840 161218560 83886080 89784320 t = true :=
  ⟨_, (join_sr (m := 86835200) (by decide) (join_su (m := 160563200) (by decide) (join_sr (m := 85360640) (by decide) (join_su (m := 160235520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 160235520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 85360640) (by decide) (join_su (m := 160890880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 160890880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 160563200) (by decide) (join_sr (m := 88309760) (by decide) (join_su (m := 160235520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 160235520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 88309760) (by decide) (join_su (m := 160890880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 160890880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (61/320 : ℝ) (123/640 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e1 : (((161218560 : ℤ) : ℝ) / (D : ℝ)) = (123/640 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

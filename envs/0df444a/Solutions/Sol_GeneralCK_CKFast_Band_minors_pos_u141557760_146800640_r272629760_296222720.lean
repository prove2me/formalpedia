-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u141557760_146800640_r272629760_296222720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:44:10.510314+00:00
-- url     : https://prove2.me/submissions/02b61083-9545-459d-9457-33e8f6613db7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [27/160, 7/40]`, `ρ ∈ [13/40, 113/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 141557760 142868480 272629760 278528000 ⟨⟨155857651465, 155857651475⟩, ⟨150154473043, 161657840404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 142868480 144179200 272629760 278528000 ⟨⟨154643193540, 154643193548⟩, ⟨148979405577, 160403041209⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 141557760 142868480 278528000 284426240 ⟨⟨158770229741, 158770229751⟩, ⟨153048971514, 164588011560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 142868480 144179200 278528000 284426240 ⟨⟨157538750013, 157538750021⟩, ⟨151856822723, 163316267311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 144179200 145489920 272629760 278528000 ⟨⟨153439133734, 153439133743⟩, ⟨147814248177, 159159142489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 145489920 146800640 272629760 278528000 ⟨⟨152245293478, 152245293488⟩, ⟨146658831560, 157925956100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 144179200 145489920 278528000 284426240 ⟨⟨156317701908, 156317701916⟩, ⟨150674622512, 162055451555⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 145489920 146800640 278528000 284426240 ⟨⟨155106907534, 155106907544⟩, ⟨149502202109, 160805377005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 141557760 142868480 284426240 290324480 ⟨⟨161669718721, 161669718731⟩, ⟨155930584430, 167504888988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 142868480 144179200 284426240 290324480 ⟨⟨160421458021, 160421458029⟩, ⟨154721591121, 166216444423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 141557760 142868480 290324480 296222720 ⟨⟨164556335725, 164556335735⟩, ⟨158799524351, 170408694818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 142868480 144179200 290324480 296222720 ⟨⟨163291529290, 163291529298⟩, ⟨157573917892, 169103788920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 144179200 145489920 284426240 290324480 ⟨⟨159183658600, 159183658609⟩, ⟨153522581101, 164938952485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 145489920 146800640 284426240 290324480 ⟨⟨157956143296, 157956143306⟩, ⟨152333386149, 163672226807⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 144179200 145489920 290324480 296222720 ⟨⟨162037210078, 162037210086⟩, ⟨156358325744, 167809856050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 145489920 146800640 290324480 296222720 ⟨⟨160793201712, 160793201722⟩, ⟨155152580306, 166526710812⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 141557760 146800640 272629760 296222720 t = true :=
  ⟨_, (join_sr (m := 284426240) (by decide) (join_su (m := 144179200) (by decide) (join_sr (m := 278528000) (by decide) (join_su (m := 142868480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 142868480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 278528000) (by decide) (join_su (m := 145489920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 145489920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 144179200) (by decide) (join_sr (m := 290324480) (by decide) (join_su (m := 142868480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 142868480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 290324480) (by decide) (join_su (m := 145489920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 145489920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (27/160 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (13/40 : ℝ) (113/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  have e3 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

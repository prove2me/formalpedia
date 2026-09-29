-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u152043520_157286400_r272629760_296222720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:59:23.395137+00:00
-- url     : https://prove2.me/submissions/cd99d352-474d-46dc-b760-259270ea0f02

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [29/160, 3/16]`, `ρ ∈ [13/40, 113/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 152043520 153354240 272629760 278528000 ⟨⟨146423410288, 146423410298⟩, ⟨141022194408, 151914415048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 153354240 154664960 272629760 278528000 ⟨⟨145287354382, 145287354387⟩, ⟨139921872126, 150741781455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 152043520 153354240 278528000 284426240 ⟨⟨149200787219, 149200787229⟩, ⟨143781146393, 154709855223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 153354240 154664960 278528000 284426240 ⟨⟨148047994183, 148047994187⟩, ⟨142664063018, 153520522242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 154664960 155975680 272629760 278528000 ⟨⟨144160374243, 144160374252⟩, ⟨138830205763, 149578655676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 155975680 157286400 272629760 278528000 ⟨⟨143042320385, 143042320395⟩, ⟨137747053438, 148424880370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 154664960 155975680 278528000 284426240 ⟨⟨146904314712, 146904314719⟩, ⟨141555677140, 152340730719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 155975680 157286400 278528000 284426240 ⟨⟨145769599695, 145769599704⟩, ⟨140455847126, 151170323827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 152043520 153354240 284426240 290324480 ⟨⟨151966896747, 151966896754⟩, ⟨146529003607, 157493853908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 153354240 154664960 284426240 290324480 ⟨⟨150797578116, 150797578120⟩, ⟨145395366971, 156288036717⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 152043520 153354240 290324480 296222720 ⟨⟨154721915167, 154721915176⟩, ⟨149265938690, 160266591103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 153354240 154664960 290324480 296222720 ⟨⟨153536277920, 153536277922⟩, ⟨148115952186, 159044500194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 154664960 155975680 284426240 290324480 ⟨⟨149637407422, 149637407432⟩, ⟨144270466030, 155091791160⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 155975680 157286400 284426240 290324480 ⟨⟨148486235983, 148486235992⟩, ⟨143154159444, 153904960980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 154664960 155975680 290324480 296222720 ⟨⟨152359819667, 152359819677⟩, ⟨146974736301, 157832007748⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 155975680 157286400 290324480 296222720 ⟨⟨151192392206, 151192392214⟩, ⟨145842150042, 156628958125⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 152043520 157286400 272629760 296222720 t = true :=
  ⟨_, (join_sr (m := 284426240) (by decide) (join_su (m := 154664960) (by decide) (join_sr (m := 278528000) (by decide) (join_su (m := 153354240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 153354240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 278528000) (by decide) (join_su (m := 155975680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 155975680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 154664960) (by decide) (join_sr (m := 290324480) (by decide) (join_su (m := 153354240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 153354240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 290324480) (by decide) (join_su (m := 155975680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 155975680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (29/160 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (13/40 : ℝ) (113/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  have e3 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

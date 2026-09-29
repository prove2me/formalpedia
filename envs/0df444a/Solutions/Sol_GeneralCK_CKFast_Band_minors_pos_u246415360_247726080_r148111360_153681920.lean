-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_247726080_r148111360_153681920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T10:57:58.835332+00:00
-- url     : https://prove2.me/submissions/73b20b3f-531f-4552-93e2-6b6e19e93f29

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 189/640]`, `ρ ∈ [113/640, 469/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 246743040 148111360 149504000 ⟨⟨44871156792, 44871156795⟩, ⟨44066388484, 45678847138⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246743040 247070720 148111360 149504000 ⟨⟨44765823475, 44765823480⟩, ⟨43962037181, 45572526107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246415360 246743040 149504000 150896640 ⟨⟨45281282041, 45281282043⟩, ⟨44475598083, 46089889500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 246743040 247070720 149504000 150896640 ⟨⟨45175029249, 45175029254⟩, ⟨44370328720, 45982647585⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 247070720 247398400 148111360 149504000 ⟨⟨44660627978, 44660627984⟩, ⟨43857821567, 45466345044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 247398400 247726080 148111360 149504000 ⟨⟨44555569789, 44555569795⟩, ⟨43753741136, 45360303430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247070720 247398400 149504000 150896640 ⟨⟨45068915199, 45068915205⟩, ⟨44265195967, 45875546559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247398400 247726080 149504000 150896640 ⟨⟨44962939372, 44962939378⟩, ⟨44160199308, 45768585903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 246415360 246743040 150896640 152289280 ⟨⟨45691239938, 45691239941⟩, ⟨44884640572, 46500764267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 246743040 247070720 150896640 152289280 ⟨⟨45584068781, 45584068786⟩, ⟨44778454253, 46392602580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 246415360 246743040 152289280 153681920 ⟨⟨46101030865, 46101030867⟩, ⟨45293516328, 46911471820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 246743040 247070720 152289280 153681920 ⟨⟨45992942444, 45992942449⟩, ⟨45186414153, 46802391470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 247070720 247398400 150896640 152289280 ⟨⟨45477037277, 45477037282⟩, ⟨44672405454, 46284582698⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 247398400 247726080 150896640 152289280 ⟨⟨45370144909, 45370144914⟩, ⟨44566493662, 46176704096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 247070720 247398400 152289280 153681920 ⟨⟨45884994586, 45884994591⟩, ⟨45079450403, 46693453833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 247398400 247726080 152289280 153681920 ⟨⟨45777186768, 45777186773⟩, ⟨44972624564, 46584658384⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 247726080 148111360 153681920 t = true :=
  ⟨_, (join_sr (m := 150896640) (by decide) (join_su (m := 247070720) (by decide) (join_sr (m := 149504000) (by decide) (join_su (m := 246743040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 246743040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 149504000) (by decide) (join_su (m := 247398400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 247398400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 247070720) (by decide) (join_sr (m := 152289280) (by decide) (join_su (m := 246743040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 246743040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 152289280) (by decide) (join_su (m := 247398400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 247398400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (189/640 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((247726080 : ℤ) : ℝ) / (D : ℝ)) = (189/640 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

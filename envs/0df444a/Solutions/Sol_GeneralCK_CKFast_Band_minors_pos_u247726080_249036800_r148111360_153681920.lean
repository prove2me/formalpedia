-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u247726080_249036800_r148111360_153681920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T10:58:38.672257+00:00
-- url     : https://prove2.me/submissions/33e01e8f-0c2a-4854-bba0-f303370d1f44

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [189/640, 19/64]`, `ρ ∈ [113/640, 469/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 247726080 248053760 148111360 149504000 ⟨⟨44450648394, 44450648399⟩, ⟨43649795381, 45254400748⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 248053760 248381440 148111360 149504000 ⟨⟨44345863285, 44345863288⟩, ⟨43545983804, 45148636474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247726080 248053760 149504000 150896640 ⟨⟨44857101254, 44857101259⟩, ⟨44055338239, 45661765090⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 248053760 248381440 149504000 150896640 ⟨⟨44751400332, 44751400335⟩, ⟨43950612258, 45555083599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 248381440 248709120 148111360 149504000 ⟨⟨44241213951, 44241213956⟩, ⟨43442305901, 45043010098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 248709120 249036800 148111360 149504000 ⟨⟨44136699889, 44136699894⟩, ⟨43338761178, 44937521102⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 248381440 248709120 149504000 150896640 ⟨⟨44645836093, 44645836098⟩, ⟨43846020857, 45448540917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 248709120 249036800 149504000 150896640 ⟨⟨44540408031, 44540408036⟩, ⟨43741563541, 45342136521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 247726080 248053760 150896640 152289280 ⟨⟨45263391155, 45263391161⟩, ⟨44460718364, 46068966249⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 248053760 248381440 150896640 152289280 ⟨⟨45156775505, 45156775508⟩, ⟨44355079058, 45961368630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 247726080 248053760 152289280 153681920 ⟨⟨45669518467, 45669518472⟩, ⟨44865936121, 46476004592⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 248053760 248381440 152289280 153681920 ⟨⟨45561989169, 45561989170⟩, ⟨44759384566, 46367491930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 248381440 248709120 150896640 152289280 ⟨⟨45050297439, 45050297444⟩, ⟨44249575234, 45853910723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 248709120 249036800 150896640 152289280 ⟨⟨44943956449, 44943956455⟩, ⟨44144206390, 45746592003⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 248381440 248709120 152289280 153681920 ⟨⟨45454598350, 45454598355⟩, ⟨44652969388, 46259119877⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 248709120 249036800 152289280 153681920 ⟨⟨45347345503, 45347345508⟩, ⟨44546690083, 46150887907⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 247726080 249036800 148111360 153681920 t = true :=
  ⟨_, (join_sr (m := 150896640) (by decide) (join_su (m := 248381440) (by decide) (join_sr (m := 149504000) (by decide) (join_su (m := 248053760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 248053760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 149504000) (by decide) (join_su (m := 248709120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 248709120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 248381440) (by decide) (join_sr (m := 152289280) (by decide) (join_su (m := 248053760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 248053760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 152289280) (by decide) (join_su (m := 248709120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 248709120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (189/640 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((247726080 : ℤ) : ℝ) / (D : ℝ)) = (189/640 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

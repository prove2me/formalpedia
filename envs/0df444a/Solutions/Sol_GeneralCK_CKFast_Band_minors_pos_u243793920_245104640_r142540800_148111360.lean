-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_245104640_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:38:03.273173+00:00
-- url     : https://prove2.me/submissions/5d6cc421-9997-4949-ae4e-140b36cf4d01

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 187/640]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 243793920 244121600 142540800 143933440 ⟨⟨44047016802, 44047016809⟩, ⟨43238025572, 44858970628⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 244121600 244449280 142540800 143933440 ⟨⟨43944281549, 43944281555⟩, ⟨43136283914, 44755235909⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 243793920 244121600 143933440 145326080 ⟨⟨44465241073, 44465241078⟩, ⟨43655321707, 45278124467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244121600 244449280 143933440 145326080 ⟨⟨44361574226, 44361574231⟩, ⟨43552649901, 45173456714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 244449280 244776960 142540800 143933440 ⟨⟨43841684467, 43841684472⟩, ⟨43034678236, 44651641569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 244776960 245104640 142540800 143933440 ⟨⟨43739225037, 43739225040⟩, ⟨42933208035, 44548187079⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 244449280 244776960 143933440 145326080 ⟨⟨44258046518, 44258046523⟩, ⟨43450115043, 45068930311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 244776960 245104640 143933440 145326080 ⟨⟨44154657429, 44154657432⟩, ⟨43347716623, 44964544723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 244121600 145326080 146718720 ⟨⟨44883287290, 44883287295⟩, ⟨44072440068, 45697099972⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 244121600 244449280 145326080 146718720 ⟨⟨44778690018, 44778690023⟩, ⟨43968839279, 45591500358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243793920 244121600 146718720 148111360 ⟨⟨45301155860, 45301155866⟩, ⟨44489381062, 46115897549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 244121600 244449280 146718720 148111360 ⟨⟨45195629331, 45195629336⟩, ⟨44384852450, 46009367247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 244449280 244776960 145326080 146718720 ⟨⟨44674232848, 44674232853⟩, ⟨43865376398, 45486043058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 244776960 245104640 145326080 146718720 ⟨⟨44569915256, 44569915258⟩, ⟨43762050912, 45380727535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 244449280 244776960 146718720 148111360 ⟨⟨45090243857, 45090243864⟩, ⟨44280462701, 45902980214⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 244776960 245104640 146718720 148111360 ⟨⟨44984998915, 44984998918⟩, ⟨44176211299, 45796735911⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 245104640 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 244449280) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 244121600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 244121600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 244776960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 244776960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 244449280) (by decide) (join_sr (m := 146718720) (by decide) (join_su (m := 244121600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 244121600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 146718720) (by decide) (join_su (m := 244776960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 244776960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (187/640 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((245104640 : ℤ) : ℝ) / (D : ℝ)) = (187/640 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

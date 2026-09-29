-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_247726080_r125829120_128614400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:39:55.360192+00:00
-- url     : https://prove2.me/submissions/888338ab-326d-4678-8421-77735385402f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 189/640]`, `ρ ∈ [3/20, 157/1024]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 246743040 125829120 126525440 ⟨⟨38182839885, 38182839887⟩, ⟨37507002478, 38860711584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246415360 246743040 126525440 127221760 ⟨⟨38389310850, 38389310851⟩, ⟨37713048292, 39067608469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246743040 247070720 125829120 126525440 ⟨⟨38092605894, 38092605900⟩, ⟨37417435274, 38769807422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 246743040 247070720 126525440 127221760 ⟨⟨38298607759, 38298607764⟩, ⟨37623012601, 38976234595⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 246415360 246743040 127221760 127918080 ⟨⟨38595738360, 38595738363⟩, ⟨37919050686, 39274461867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246415360 246743040 127918080 128614400 ⟨⟨38802122468, 38802122471⟩, ⟨38125009707, 39481271829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 246743040 247070720 127221760 127918080 ⟨⟨38504566461, 38504566466⟩, ⟨37828546796, 39182618572⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 246743040 247070720 127918080 128614400 ⟨⟨38710482048, 38710482053⟩, ⟨38034037910, 39388959402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 247070720 247398400 125829120 126525440 ⟨⟨38002493932, 38002493937⟩, ⟨37327988499, 38679026894⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 247070720 247398400 126525440 127221760 ⟨⟨38208027207, 38208027212⟩, ⟨37533097849, 38884984865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 247398400 247726080 125829120 126525440 ⟨⟨37912503534, 37912503539⟩, ⟨37238661695, 38588369533⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 247398400 247726080 126525440 127221760 ⟨⟨38117568727, 38117568732⟩, ⟨37443303576, 38793858812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 247070720 247398400 127221760 127918080 ⟨⟨38413517607, 38413517612⟩, ⟨37738164355, 39090899930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 247070720 247398400 127918080 128614400 ⟨⟨38618965181, 38618965186⟩, ⟨37943188066, 39296772137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 247398400 247726080 127221760 127918080 ⟨⟨38322591333, 38322591338⟩, ⟨37647902899, 38999305473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 247398400 247726080 127918080 128614400 ⟨⟨38527571400, 38527571405⟩, ⟨37852459712, 39204709563⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 247726080 125829120 128614400 t = true :=
  ⟨_, (join_su (m := 247070720) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 246743040) (by decide) (join_sr (m := 126525440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 126525440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 246743040) (by decide) (join_sr (m := 127918080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 127918080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 127221760) (by decide) (join_su (m := 247398400) (by decide) (join_sr (m := 126525440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 126525440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 247398400) (by decide) (join_sr (m := 127918080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 127918080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (189/640 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (157/1024 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((247726080 : ℤ) : ℝ) / (D : ℝ)) = (189/640 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((128614400 : ℤ) : ℝ) / (D : ℝ)) = (157/1024 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

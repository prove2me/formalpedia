-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u165150720_167772160_r101580800_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:24:16.852974+00:00
-- url     : https://prove2.me/submissions/d859f38a-2de2-44d2-9910-1d3a068b4b27

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [63/320, 1/5]`, `ρ ∈ [31/256, 41/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 165150720 165806080 101580800 103055360 ⟨⟨53978789262, 53978789266⟩, ⟨52177771426, 55793867968⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 165150720 165806080 103055360 104529920 ⟨⟨54720959079, 54720959083⟩, ⟨52917283909, 56538692982⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 165806080 166461440 101580800 103055360 ⟨⟨53741904494, 53741904501⟩, ⟨51946269546, 55551524411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 165806080 166461440 103055360 104529920 ⟨⟨54481090190, 54481090197⟩, ⟨52682806072, 56293357314⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 165150720 165806080 104529920 106004480 ⟨⟨55462207685, 55462207687⟩, ⟨53655881076, 57282590840⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 165150720 165806080 106004480 107479040 ⟨⟨56202538697, 56202538701⟩, ⟨54393566521, 58025565193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 165806080 166461440 104529920 106004480 ⟨⟨55219365299, 55219365305⟩, ⟨53418437816, 57034273778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 165806080 166461440 106004480 107479040 ⟨⟨55956733380, 55956733388⟩, ⟨54153168308, 57774277395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 166461440 167116800 101580800 103055360 ⟨⟨53506203119, 53506203127⟩, ⟨51715913651, 55310402372⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 166461440 167116800 103055360 104529920 ⟨⟨54242416516, 54242416524⟩, ⟨52449486026, 56049254999⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 167116800 167772160 101580800 103055360 ⟨⟨53271673634, 53271673640⟩, ⟨51486692631, 55070489939⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 167116800 167772160 103055360 104529920 ⟨⟨54004926461, 54004926468⟩, ⟨52217312565, 55806374035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 166461440 167116800 104529920 106004480 ⟨⟨54977729831, 54977729837⟩, ⟨53182164029, 56787201784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 166461440 167116800 106004480 107479040 ⟨⟨55712146563, 55712146569⟩, ⟨53913951136, 57524246260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 167116800 167772160 104529920 106004480 ⟨⟨54737289589, 54737289595⟩, ⟨52947048421, 56541362767⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 167116800 167772160 106004480 107479040 ⟨⟨55468766464, 55468766471⟩, ⟨53675903618, 57275459606⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 165150720 167772160 101580800 107479040 t = true :=
  ⟨_, (join_su (m := 166461440) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 165806080) (by decide) (join_sr (m := 103055360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 103055360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 165806080) (by decide) (join_sr (m := 106004480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 106004480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 104529920) (by decide) (join_su (m := 167116800) (by decide) (join_sr (m := 103055360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 103055360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 167116800) (by decide) (join_sr (m := 106004480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 106004480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (63/320 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (31/256 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((101580800 : ℤ) : ℝ) / (D : ℝ)) = (31/256 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

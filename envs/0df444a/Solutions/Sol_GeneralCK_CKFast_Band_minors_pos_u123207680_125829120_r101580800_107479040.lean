-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u123207680_125829120_r101580800_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:19:08.299523+00:00
-- url     : https://prove2.me/submissions/234912e7-1d1f-4155-90e7-81e47c378a0c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/320, 3/20]`, `ρ ∈ [31/256, 41/320]` by 12 cells of the computing
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
theorem cell0 : cellOK 123207680 123863040 101580800 103055360 ⟨⟨72270722918, 72270722927⟩, ⟨70023650590, 74538784670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 123207680 123863040 103055360 104529920 ⟨⟨73233506463, 73233506472⟩, ⟨70983245425, 75504733053⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 123863040 124518400 101580800 103055360 ⟨⟨71925045818, 71925045827⟩, ⟨69686934816, 74183995108⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 123863040 124518400 103055360 104529920 ⟨⟨72883846685, 72883846692⟩, ⟨70642554640, 75145953732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 123207680 123863040 104529920 107479040 ⟨⟨74674037073, 74674037082⟩, ⟨71811593622, 77570422998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 123863040 124518400 104529920 107479040 ⟨⟨74318446387, 74318446394⟩, ⟨71468348135, 77202226878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 124518400 125173760 101580800 103055360 ⟨⟨71581750419, 71581750428⟩, ⟨69352519495, 73831670326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 124518400 125173760 103055360 104529920 ⟨⟨72536588715, 72536588724⟩, ⟨70304184479, 74789659230⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 125173760 125829120 101580800 103055360 ⟨⟨71240807630, 71240807639⟩, ⟨69020376656, 73481780088⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 125173760 125829120 103055360 104529920 ⟨⟨72191703292, 72191703301⟩, ⟨69968106789, 74435819142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 124518400 125173760 104529920 107479040 ⟨⟨73965287121, 73965287130⟩, ⟨71127425245, 76836574160⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 125173760 125829120 104529920 107479040 ⟨⟨73614529764, 73614529771⟩, ⟨70788796923, 76473433791⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 123207680 125829120 101580800 107479040 t = true :=
  ⟨_, (join_su (m := 124518400) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 123863040) (by decide) (join_sr (m := 103055360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 103055360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 123863040) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 104529920) (by decide) (join_su (m := 125173760) (by decide) (join_sr (m := 103055360) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 103055360) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 125173760) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/320 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (31/256 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((123207680 : ℤ) : ℝ) / (D : ℝ)) = (47/320 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((101580800 : ℤ) : ℝ) / (D : ℝ)) = (31/256 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

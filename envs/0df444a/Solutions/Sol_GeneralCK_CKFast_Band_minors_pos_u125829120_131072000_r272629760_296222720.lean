-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_131072000_r272629760_296222720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:43:30.421103+00:00
-- url     : https://prove2.me/submissions/670a1b43-c773-415b-88b8-54c7d4e8a9b2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 5/32]`, `ρ ∈ [13/40, 113/320]` by 12 cells of the computing
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
theorem cell0 : cellOK 125829120 127139840 272629760 278528000 ⟨⟨171313259216, 171313259224⟩, ⟨165095591340, 177640578192⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 127139840 128450560 272629760 278528000 ⟨⟨169958450562, 169958450566⟩, ⟨163786850628, 176238553847⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 125829120 127139840 278528000 284426240 ⟨⟨174432396680, 174432396688⟩, ⟨168197827518, 180775879876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 127139840 128450560 278528000 284426240 ⟨⟨173060235994, 173060235999⟩, ⟨166871598829, 179356663761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 128450560 129761280 272629760 278528000 ⟨⟨168616545920, 168616545930⟩, ⟨162490393128, 174850072712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 129761280 131072000 272629760 278528000 ⟨⟨167287307483, 167287307493⟩, ⟨161205993794, 173474883810⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 128450560 129761280 278528000 284426240 ⟨⟨171701000437, 171701000447⟩, ⟨165557682168, 177951003569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 129761280 131072000 278528000 284426240 ⟨⟨170354453592, 170354453602⟩, ⟨164255853609, 176558650017⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 125829120 128450560 284426240 290324480 ⟨⟨176838990542, 176838990551⟩, ⟨166909073696, 187045548053⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 125829120 128450560 290324480 296222720 ⟨⟨179917434556, 179917434564⟩, ⟨169955894756, 190154066432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 128450560 131072000 284426240 290324480 ⟨⟨174086372786, 174086372796⟩, ⟨164288011425, 184156312284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 128450560 131072000 290324480 296222720 ⟨⟨177131288338, 177131288348⟩, ⟨167300946933, 187231767589⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 131072000 272629760 296222720 t = true :=
  ⟨_, (join_sr (m := 284426240) (by decide) (join_su (m := 128450560) (by decide) (join_sr (m := 278528000) (by decide) (join_su (m := 127139840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 127139840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 278528000) (by decide) (join_su (m := 129761280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 129761280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 128450560) (by decide) (join_sr (m := 290324480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 290324480) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (5/32 : ℝ) →
    rho ∈ Set.Icc (13/40 : ℝ) (113/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e2 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  have e3 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

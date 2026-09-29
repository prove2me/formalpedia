-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_131072000_r201850880_225443840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:34:08.661067+00:00
-- url     : https://prove2.me/submissions/b4fff37f-105f-4d4a-aa70-c50231e6e604

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 5/32]`, `ρ ∈ [77/320, 43/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 125829120 127139840 201850880 207749120 ⟨⟨132494540583, 132494540592⟩, ⟨126502365520, 138605317761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 127139840 128450560 201850880 207749120 ⟨⟨131373820874, 131373820876⟩, ⟨125428919717, 137435863633⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 125829120 127139840 207749120 213647360 ⟨⟨135835034452, 135835034460⟩, ⟨129822277467, 141965641681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 127139840 128450560 207749120 213647360 ⟨⟨134692774012, 134692774018⟩, ⟨128727226779, 140774738535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 128450560 129761280 201850880 207749120 ⟨⟨130265313585, 130265313594⟩, ⟨124366976188, 136279360169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 129761280 131072000 201850880 207749120 ⟨⟨129168771145, 129168771155⟩, ⟨123316303627, 135135542785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 128450560 129761280 207749120 213647360 ⟨⟨133562820367, 133562820376⟩, ⟨127643779775, 139596872481⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 129761280 131072000 207749120 213647360 ⟨⟨132444926091, 132444926101⟩, ⟨126571705000, 138431779417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 125829120 127139840 213647360 219545600 ⟨⟨139155093577, 139155093585⟩, ⟨133122112037, 145305174285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 127139840 128450560 213647360 219545600 ⟨⟨137991696740, 137991696744⟩, ⟨132005853100, 144093233877⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 125829120 127139840 219545600 225443840 ⟨⟨142455107929, 142455107939⟩, ⟨136402248960, 148624315889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 127139840 128450560 219545600 225443840 ⟨⟨141270967868, 141270967872⟩, ⟨135265167614, 147391738453⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 128450560 129761280 213647360 219545600 ⟨⟨136840693388, 136840693398⟩, ⟨130901291690, 142894409215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 129761280 131072000 213647360 219545600 ⟨⟨135701836405, 135701836413⟩, ⟨129808196350, 141708436840⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 128450560 129761280 219545600 225443840 ⟨⟨140099300638, 140099300647⟩, ⟨134139870386, 146172347996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 129761280 131072000 219545600 225443840 ⟨⟨138939859565, 138939859573⟩, ⟨133026125962, 144965881833⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 131072000 201850880 225443840 t = true :=
  ⟨_, (join_sr (m := 213647360) (by decide) (join_su (m := 128450560) (by decide) (join_sr (m := 207749120) (by decide) (join_su (m := 127139840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 127139840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 207749120) (by decide) (join_su (m := 129761280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 129761280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 128450560) (by decide) (join_sr (m := 219545600) (by decide) (join_su (m := 127139840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 127139840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 219545600) (by decide) (join_su (m := 129761280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 129761280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (5/32 : ℝ) →
    rho ∈ Set.Icc (77/320 : ℝ) (43/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e2 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e3 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

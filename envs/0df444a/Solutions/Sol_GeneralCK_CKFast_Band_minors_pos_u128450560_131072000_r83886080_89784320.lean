-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u128450560_131072000_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:52:33.202345+00:00
-- url     : https://prove2.me/submissions/18379afb-76b8-4437-8a1f-960aac8d3c39

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [49/320, 5/32]`, `ρ ∈ [1/10, 137/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 128450560 129105920 83886080 85360640 ⟨⟨58251215997, 58251216005⟩, ⟨56112254105, 60410236424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 128450560 129105920 85360640 86835200 ⟨⟨59204670685, 59204670692⟩, ⟨57062407684, 61366973562⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 129105920 129761280 83886080 85360640 ⟨⟨57971404027, 57971404030⟩, ⟨55840669899, 60122053393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 129105920 129761280 85360640 86835200 ⟨⟨58920769740, 58920769744⟩, ⟨56786745234, 61074691329⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 128450560 129105920 86835200 88309760 ⟨⟨60156239696, 60156239705⟩, ⟨58010690812, 62321809730⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 128450560 129105920 88309760 89784320 ⟨⟨61105933100, 61105933107⟩, ⟨58957113435, 63274755111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 129105920 129761280 86835200 88309760 ⟨⟨59868272597, 59868272601⟩, ⟨57730972700, 62025451350⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 129105920 129761280 88309760 89784320 ⟨⟨60813922484, 60813922488⟩, ⟨58673362067, 62974343457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 129761280 130416640 83886080 85360640 ⟨⟨57693507071, 57693507077⟩, ⟨55570927644, 59835860181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 129761280 130416640 85360640 86835200 ⟨⟨58638805961, 58638805968⟩, ⟨56512946884, 60784421056⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 130416640 131072000 83886080 85360640 ⟨⟨57417501836, 57417501845⟩, ⟨55303005028, 59551632470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 130416640 131072000 85360640 86835200 ⟨⟨58358755841, 58358755848⟩, ⟨56240990107, 60496138216⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 129761280 130416640 86835200 88309760 ⟨⟨59582264511, 59582264520⟩, ⟨57453140538, 61731126767⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 129761280 130416640 88309760 89784320 ⟨⟨60523892437, 60523892443⟩, ⟨58391518209, 62675987137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 130416640 131072000 86835200 88309760 ⟨⟨59298191729, 59298191736⟩, ⟨57177171594, 61438811251⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 130416640 131072000 88309760 89784320 ⟨⟨60235819041, 60235819048⟩, ⟨58111558920, 62379661222⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 128450560 131072000 83886080 89784320 t = true :=
  ⟨_, (join_su (m := 129761280) (by decide) (join_sr (m := 86835200) (by decide) (join_su (m := 129105920) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 85360640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 129105920) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 88309760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 86835200) (by decide) (join_su (m := 130416640) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 85360640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 130416640) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 88309760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (49/320 : ℝ) (5/32 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((128450560 : ℤ) : ℝ) / (D : ℝ)) = (49/320 : ℝ) := by norm_num [D]
  have e1 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

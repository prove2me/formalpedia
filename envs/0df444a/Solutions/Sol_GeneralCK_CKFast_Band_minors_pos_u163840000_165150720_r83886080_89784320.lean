-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u163840000_165150720_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:18:05.081076+00:00
-- url     : https://prove2.me/submissions/e0df26bd-c8d4-4c5e-9a49-1a5994904166

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [25/128, 63/320]`, `ρ ∈ [1/10, 137/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 163840000 164167680 83886080 85360640 ⟨⟨45453886878, 45453886884⟩, ⟨44343205190, 46570184453⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 164167680 164495360 83886080 85360640 ⟨⟨45352462118, 45352462126⟩, ⟨44243667971, 46466854791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 163840000 164167680 85360640 86835200 ⟨⟨46214461277, 46214461283⟩, ⟨45102210661, 47332325179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 164167680 164495360 85360640 86835200 ⟨⟨46111461413, 46111461419⟩, ⟨45001101237, 47227417554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 164495360 164823040 83886080 85360640 ⟨⟨45251302525, 45251302529⟩, ⟨44144389456, 46363796838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 164823040 165150720 83886080 85360640 ⟨⟨45150406757, 45150406763⟩, ⟨44045368342, 46261009225⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 164495360 164823040 85360640 86835200 ⟨⟨46008730131, 46008730134⟩, ⟨44900253932, 47122785058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 164823040 165150720 85360640 86835200 ⟨⟨45906266077, 45906266083⟩, ⟨44799667423, 47018426310⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 163840000 164167680 86835200 88309760 ⟨⟨46974043561, 46974043569⟩, ⟨45860228403, 48093469393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 164167680 164495360 86835200 88309760 ⟨⟨46869474442, 46869474450⟩, ⟨45757552592, 47986989689⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 163840000 164167680 88309760 89784320 ⟨⟨47732637719, 47732637726⟩, ⟨46617262379, 48853621103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 164167680 164495360 88309760 89784320 ⟨⟨47626505163, 47626505169⟩, ⟨46513025962, 48745575172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 164495360 164823040 86835200 88309760 ⟨⟨46765177289, 46765177292⟩, ⟨45655142275, 47880788500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 164823040 165150720 86835200 88309760 ⟨⟨46661150731, 46661150737⟩, ⟨45552996120, 47774864434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 164495360 164823040 88309760 89784320 ⟨⟨47520647919, 47520647923⟩, ⟨46409058384, 48637811109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 164823040 165150720 88309760 89784320 ⟨⟨47415064606, 47415064612⟩, ⟨46305358295, 48530327505⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 163840000 165150720 83886080 89784320 t = true :=
  ⟨_, (join_sr (m := 86835200) (by decide) (join_su (m := 164495360) (by decide) (join_sr (m := 85360640) (by decide) (join_su (m := 164167680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 164167680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 85360640) (by decide) (join_su (m := 164823040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 164823040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 164495360) (by decide) (join_sr (m := 88309760) (by decide) (join_su (m := 164167680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 164167680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 88309760) (by decide) (join_su (m := 164823040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 164823040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (25/128 : ℝ) (63/320 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((163840000 : ℤ) : ℝ) / (D : ℝ)) = (25/128 : ℝ) := by norm_num [D]
  have e1 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

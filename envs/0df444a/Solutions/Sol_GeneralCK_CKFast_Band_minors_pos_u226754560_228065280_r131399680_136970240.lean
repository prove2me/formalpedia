-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u226754560_228065280_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:55:21.731491+00:00
-- url     : https://prove2.me/submissions/32042d23-0c59-4d60-9a54-35ea95c94c24

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [173/640, 87/320]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 226754560 227082240 131399680 132792320 ⟨⟨45839612335, 45839612336⟩, ⟨44983791445, 46698720362⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 227082240 227409920 131399680 132792320 ⟨⟨45736868744, 45736868750⟩, ⟨44882154834, 46594862754⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 226754560 227082240 132792320 134184960 ⟨⟨46309702406, 46309702410⟩, ⟨45452871274, 47169821808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 227082240 227409920 132792320 134184960 ⟨⟨46205959864, 46205959869⟩, ⟨45350237297, 47064963669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 227409920 227737600 131399680 132792320 ⟨⟨45634284078, 45634284085⟩, ⟨44780674499, 46491166742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 227737600 228065280 131399680 132792320 ⟨⟨45531857719, 45531857726⟩, ⟨44679349828, 46387631701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 227409920 227737600 132792320 134184960 ⟨⟨46102377453, 46102377459⟩, ⟨45247760801, 46960268336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 227737600 228065280 132792320 134184960 ⟨⟨45998954555, 45998954562⟩, ⟨45145441173, 46855735182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 226754560 227082240 134184960 135577600 ⟨⟨46779539223, 46779539226⟩, ⟨45921698431, 47640669413⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 227082240 227409920 134184960 135577600 ⟨⟨46674799305, 46674799310⟩, ⟨45818068656, 47534812327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 226754560 227082240 135577600 136970240 ⟨⟨47249123417, 47249123421⟩, ⟨46390273544, 48111263809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 227082240 227409920 135577600 136970240 ⟨⟨47143387698, 47143387704⟩, ⟨46285649542, 48004409358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 227409920 227737600 134184960 135577600 ⟨⟨46570220722, 46570220727⟩, ⟨45714597565, 47429119251⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 227737600 228065280 134184960 135577600 ⟨⟨46465802846, 46465802852⟩, ⟨45611284535, 47323589551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 227409920 227737600 135577600 136970240 ⟨⟨47037814505, 47037814512⟩, ⟨46181185412, 47897720109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 227737600 228065280 135577600 136970240 ⟨⟨46932403210, 46932403217⟩, ⟨46076880531, 47791195429⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 226754560 228065280 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 227409920) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 227082240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 227082240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 227737600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 227737600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 227409920) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 227082240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 227082240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 227737600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 227737600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (173/640 : ℝ) (87/320 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((226754560 : ℤ) : ℝ) / (D : ℝ)) = (173/640 : ℝ) := by norm_num [D]
  have e1 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u231997440_233308160_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:18:53.498975+00:00
-- url     : https://prove2.me/submissions/9611e197-517c-4f51-bb61-5a9b900393dc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [177/640, 89/320]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 231997440 232325120 131399680 132792320 ⟨⟨44214445476, 44214445482⟩, ⟨43376023933, 45056044363⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 232325120 232652800 131399680 132792320 ⟨⟨44114172211, 44114172218⟩, ⟨43276816462, 44954698641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231997440 232325120 132792320 134184960 ⟨⟨44668695188, 44668695194⟩, ⟨43829288543, 45511280426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 232325120 232652800 132792320 134184960 ⟨⟨44567441847, 44567441852⟩, ⟨43729102549, 45408953080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 232652800 232980480 131399680 132792320 ⟨⟨44014048331, 44014048337⟩, ⟨43177755883, 44853504816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 232980480 233308160 131399680 132792320 ⟨⟨43914073260, 43914073267⟩, ⟨43078841633, 44752462307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 232652800 232980480 132792320 134184960 ⟨⟨44466339037, 44466339042⟩, ⟨43629064594, 45306778780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 232980480 233308160 132792320 134184960 ⟨⟨44365386180, 44365386186⟩, ⟨43529174108, 45204756940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 231997440 232325120 134184960 135577600 ⟨⟨45122715927, 45122715932⟩, ⟨44282324658, 45966287032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 232325120 232652800 134184960 135577600 ⟨⟨45020483959, 45020483965⟩, ⟨44181161587, 45862979517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 231997440 232325120 135577600 136970240 ⟨⟨45576508249, 45576508254⟩, ⟨44735132835, 46421064739⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 232325120 232652800 135577600 136970240 ⟨⟨45473299101, 45473299106⟩, ⟨44632994126, 46316778509⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 232652800 232980480 134184960 135577600 ⟨⟨44918403662, 44918403667⟩, ⟨44080147691, 45759826190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 232980480 233308160 134184960 135577600 ⟨⟨44816474454, 44816474460⟩, ⟨43979282399, 45656826462⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 232652800 232980480 135577600 136970240 ⟨⟨45370242755, 45370242760⟩, ⟨44531005721, 46212647600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 232980480 233308160 135577600 136970240 ⟨⟨45267338626, 45267338632⟩, ⟨44429167047, 46108671419⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 231997440 233308160 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 232652800) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 232325120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 232325120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 232980480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 232980480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 232652800) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 232325120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 232325120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 232980480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 232980480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (177/640 : ℝ) (89/320 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((231997440 : ℤ) : ℝ) / (D : ℝ)) = (177/640 : ℝ) := by norm_num [D]
  have e1 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

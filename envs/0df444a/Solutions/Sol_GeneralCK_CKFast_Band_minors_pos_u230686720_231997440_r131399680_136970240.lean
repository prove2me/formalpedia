-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_231997440_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:18:48.938116+00:00
-- url     : https://prove2.me/submissions/edf3974d-e777-4f02-890f-89ccb364c767

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 177/640]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231014400 131399680 132792320 ⟨⟨44617043944, 44617043951⟩, ⟨43774334139, 45462957979⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 231014400 231342080 131399680 132792320 ⟨⟨44516167352, 44516167359⟩, ⟨43674533396, 45360998782⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 230686720 231014400 132792320 134184960 ⟨⟨45075225510, 45075225516⟩, ⟨44231524365, 45922132105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231014400 231342080 132792320 134184960 ⟨⟨44973364215, 44973364221⟩, ⟨44130740483, 45819186650⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 231342080 231669760 131399680 132792320 ⟨⟨44415442466, 44415442472⟩, ⟨43574881830, 45259193844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 231669760 231997440 131399680 132792320 ⟨⟨44314868704, 44314868705⟩, ⟨43475378868, 45157542566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231342080 231669760 132792320 134184960 ⟨⟨44871655788, 44871655794⟩, ⟨44030106935, 45716396617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 231669760 231997440 132792320 134184960 ⟨⟨44770099642, 44770099645⟩, ⟨43929623149, 45613761406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 230686720 231014400 134184960 135577600 ⟨⟨45533172224, 45533172229⟩, ⟨44688480242, 46381070872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231014400 231342080 134184960 135577600 ⟨⟨45430327708, 45430327713⟩, ⟨44586714694, 46277140644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 230686720 231014400 135577600 136970240 ⟨⟨45990884660, 45990884666⟩, ⟨45145202346, 46839774853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 231014400 231342080 135577600 136970240 ⟨⟨45887058399, 45887058404⟩, ⟨45042456601, 46734861340⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 231342080 231669760 134184960 135577600 ⟨⟨45327637212, 45327637219⟩, ⟨44485100633, 46173366997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 231669760 231997440 134184960 135577600 ⟨⟨45225100150, 45225100153⟩, ⟨44383637483, 46069749325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 231342080 231669760 135577600 136970240 ⟨⟨45783387306, 45783387311⟩, ⟨44939863491, 46630105554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 231669760 231997440 135577600 136970240 ⟨⟨45679870788, 45679870791⟩, ⟨44837422432, 46525506886⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 231997440 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 231342080) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 231014400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 231014400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 231669760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 231669760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 231342080) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 231014400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 231014400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 231669760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 231669760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (177/640 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((231997440 : ℤ) : ℝ) / (D : ℝ)) = (177/640 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

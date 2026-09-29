-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u233308160_234618880_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:22:14.368832+00:00
-- url     : https://prove2.me/submissions/2c9dcf7e-3e00-4eae-b2d0-fbf324afa34a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [89/320, 179/640]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 233308160 233635840 131399680 132792320 ⟨⟨43814246431, 43814246432⟩, ⟨42980073153, 44651570527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 233635840 233963520 131399680 132792320 ⟨⟨43714567266, 43714567272⟩, ⟨42881449879, 44550828901⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233308160 233635840 132792320 134184960 ⟨⟨44264582703, 44264582706⟩, ⟨43429430531, 45102886971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 233635840 233963520 132792320 134184960 ⟨⟨44163928028, 44163928033⟩, ⟨43329833292, 45001168296⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 233963520 234291200 131399680 132792320 ⟨⟨43615035206, 43615035212⟩, ⟨42782971258, 44450236851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 234291200 234618880 131399680 132792320 ⟨⟨43515649684, 43515649691⟩, ⟨42684636732, 44349793805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233963520 234291200 132792320 134184960 ⟨⟨44063421589, 44063421596⟩, ⟨43230381837, 44899600328⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 234291200 234618880 132792320 134184960 ⟨⟨43963062819, 43963062824⟩, ⟨43131075603, 44798182496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 233635840 134184960 135577600 ⟨⟨44714695758, 44714695760⟩, ⟨43878565144, 45553979738⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 233635840 233963520 134184960 135577600 ⟨⟨44613066993, 44613066998⟩, ⟨43777995356, 45451285438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 233308160 233635840 135577600 136970240 ⟨⟨45164586134, 45164586136⟩, ⟨44327477533, 46004849368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 233635840 233963520 135577600 136970240 ⟨⟨45061984693, 45061984698⟩, ⟨44225936603, 45901180865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 233963520 234291200 134184960 135577600 ⟨⟨44511587587, 44511587594⟩, ⟨43677572473, 45348742973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 234291200 234618880 134184960 135577600 ⟨⟨44410256971, 44410256976⟩, ⟨43577295931, 45246351764⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 233963520 234291200 135577600 136970240 ⟨⟨44959533729, 44959533735⟩, ⟨44124543696, 45797665315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 234291200 234618880 135577600 136970240 ⟨⟨44857232668, 44857232674⟩, ⟨44023298238, 45694302139⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 233308160 234618880 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 233963520) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 233635840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 233635840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 234291200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 234291200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 233963520) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 233635840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 233635840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 234291200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 234291200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (89/320 : ℝ) (179/640 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e1 : (((234618880 : ℤ) : ℝ) / (D : ℝ)) = (179/640 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

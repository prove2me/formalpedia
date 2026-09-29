-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_237240320_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:39:53.947986+00:00
-- url     : https://prove2.me/submissions/4f3fd131-7257-4b96-8474-6c2f0b73a1d2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 181/640]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 236257280 136970240 138362880 ⟨⟨44789884917, 44789884923⟩, ⟨43960226755, 45622647210⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 236257280 236584960 136970240 138362880 ⟨⟨44687508837, 44687508844⟩, ⟨43858893298, 45519222135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 235929600 236257280 138362880 139755520 ⟨⟨45231603348, 45231603353⟩, ⟨44400980236, 46065331904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 236257280 236584960 138362880 139755520 ⟨⟨45128266130, 45128266135⟩, ⟨44298687148, 45960944188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 236584960 236912640 136970240 138362880 ⟨⟨44585279786, 44585279788⟩, ⟨43757704483, 45415946489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 236912640 237240320 136970240 138362880 ⟨⟨44483197197, 44483197202⟩, ⟨43656659756, 45312819711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 236584960 236912640 138362880 139755520 ⟨⟨45025077013, 45025077014⟩, ⟨44196539774, 45856706977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 236912640 237240320 138362880 139755520 ⟨⟨44922035429, 44922035434⟩, ⟨44094537557, 45752619704⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 236257280 139755520 141148160 ⟨⟨45673111724, 45673111729⟩, ⟨44841524066, 46507806135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 236257280 236584960 139755520 141148160 ⟨⟨45568814710, 45568814716⟩, ⟨44738272685, 46402457127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 235929600 236257280 141148160 142540800 ⟨⟨46114410545, 46114410550⟩, ⟨45281858744, 46950070403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 236257280 236584960 141148160 142540800 ⟨⟨46009155076, 46009155083⟩, ⟨45177650406, 46843761449⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 236584960 236912640 139755520 141148160 ⟨⟨45464666865, 45464666867⟩, ⟨44635168084, 46297259693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 236912640 237240320 139755520 141148160 ⟨⟨45360667617, 45360667622⟩, ⟨44532209701, 46192213263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 236584960 236912640 141148160 142540800 ⟨⟨45904049836, 45904049839⟩, ⟨45073589905, 46737605131⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 236912640 237240320 141148160 142540800 ⟨⟨45799094249, 45799094254⟩, ⟨44969676676, 46631600875⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 237240320 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 236584960) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 236257280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 236257280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 236912640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 236912640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 236584960) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 236257280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 236257280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 236912640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 236912640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (181/640 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

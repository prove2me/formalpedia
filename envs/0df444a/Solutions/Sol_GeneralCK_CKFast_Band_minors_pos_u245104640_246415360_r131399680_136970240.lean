-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u245104640_246415360_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:28:56.477268+00:00
-- url     : https://prove2.me/submissions/29ba8193-6f28-493c-8823-30829f3f4497

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [187/640, 47/160]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 245104640 245432320 131399680 132792320 ⟨⟨40314582610, 40314582616⟩, ⟨39516941021, 41115151679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 245432320 245760000 131399680 132792320 ⟨⟨40219860430, 40219860437⟩, ⟨39423192060, 41019450448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 245104640 245432320 132792320 134184960 ⟨⟨40730487933, 40730487940⟩, ⟨39931921873, 41531982952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 245432320 245760000 132792320 134184960 ⟨⟨40634828743, 40634828750⟩, ⟨39837237377, 41435343241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 245760000 246087680 131399680 132792320 ⟨⟨40125266490, 40125266496⟩, ⟨39329569195, 40923879618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246087680 246415360 131399680 132792320 ⟨⟨40030800306, 40030800312⟩, ⟨39236071951, 40828438697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 245760000 246087680 132792320 134184960 ⟨⟨40539298800, 40539298805⟩, ⟨39742679982, 41338834938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 246087680 246415360 132792320 134184960 ⟨⟨40443897614, 40443897619⟩, ⟨39648249207, 41242457550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 245104640 245432320 134184960 135577600 ⟨⟨41146216654, 41146216661⟩, ⟨40346726388, 41948637354⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 245432320 245760000 134184960 135577600 ⟨⟨41049621626, 41049621631⟩, ⟨40251107524, 41851060337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245104640 245432320 135577600 136970240 ⟨⟨41561769174, 41561769179⟩, ⟨40761354969, 42365115287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245432320 245760000 135577600 136970240 ⟨⟨41464239473, 41464239478⟩, ⟨40664802898, 42266602136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 245760000 246087680 134184960 135577600 ⟨⟨40953156841, 40953156847⟩, ⟨40155616756, 41753615730⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 246087680 246415360 134184960 135577600 ⟨⟨40856821811, 40856821816⟩, ⟨40060253605, 41656303036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245760000 246087680 135577600 136970240 ⟨⟨41366841010, 41366841015⟩, ⟨40568379915, 42168222392⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 246087680 246415360 135577600 136970240 ⟨⟨41269573290, 41269573295⟩, ⟨40472085536, 42069975550⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 245104640 246415360 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 245760000) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 245432320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 245432320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 246087680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 246087680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 245760000) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 245432320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 245432320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 246087680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 246087680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (187/640 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((245104640 : ℤ) : ℝ) / (D : ℝ)) = (187/640 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

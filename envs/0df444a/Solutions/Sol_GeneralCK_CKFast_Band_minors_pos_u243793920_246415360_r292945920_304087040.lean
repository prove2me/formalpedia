-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_246415360_r292945920_304087040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:28:51.002756+00:00
-- url     : https://prove2.me/submissions/25a14fc7-c8d8-4784-a6d0-f05044451f04

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 47/160]`, `ρ ∈ [447/1280, 29/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 243793920 244449280 292945920 295731200 ⟨⟨88367490847, 88367490850⟩, ⟨86555282381, 90192089637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 244449280 245104640 292945920 295731200 ⟨⟨87972634529, 87972634535⟩, ⟨86164910194, 89792707841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 243793920 244449280 295731200 298516480 ⟨⟨89168794590, 89168794593⟩, ⟨87352982998, 90997005278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244449280 245104640 295731200 298516480 ⟨⟨88770651826, 88770651832⟩, ⟨86959332452, 90594329068⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 245104640 245760000 292945920 295731200 ⟨⟨87578619828, 87578619834⟩, ⟨85775362104, 89394185391⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 245760000 246415360 292945920 295731200 ⟨⟨87185441055, 87185441062⟩, ⟨85386632536, 88996516484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 245104640 245760000 295731200 298516480 ⟨⟨88373353994, 88373354000⟩, ⟨86566509338, 90192515498⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 245760000 246415360 295731200 298516480 ⟨⟨87976895395, 87976895400⟩, ⟨86174508067, 89791558758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 244449280 298516480 301301760 ⟨⟨89969549456, 89969549459⟩, ⟨88150136345, 91801370383⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 244449280 245104640 298516480 301301760 ⟨⟨89568127036, 89568127042⟩, ⟨87753214177, 91395406605⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243793920 244449280 301301760 304087040 ⟨⟨90769758103, 90769758105⟩, ⟨88946745069, 92605187620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 244449280 245104640 301301760 304087040 ⟨⟨90365062778, 90365062783⟩, ⟨88546557973, 92195943080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 245104640 245760000 298516480 301301760 ⟨⟨89167552800, 89167552806⟩, ⟨87357122708, 90990308699⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245760000 246415360 298516480 301301760 ⟨⟨88767821036, 88767821043⟩, ⟨86961856343, 90586070842⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245104640 245760000 301301760 304087040 ⟨⟨89961218824, 89961218830⟩, ⟨88147204785, 91787567579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245760000 246415360 301301760 304087040 ⟨⟨89558220521, 89558220527⟩, ⟨87748679897, 91380055285⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 246415360 292945920 304087040 t = true :=
  ⟨_, (join_sr (m := 298516480) (by decide) (join_su (m := 245104640) (by decide) (join_sr (m := 295731200) (by decide) (join_su (m := 244449280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 244449280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 295731200) (by decide) (join_su (m := 245760000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 245760000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 245104640) (by decide) (join_sr (m := 301301760) (by decide) (join_su (m := 244449280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 244449280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 301301760) (by decide) (join_su (m := 245760000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 245760000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (447/1280 : ℝ) (29/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  have e3 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

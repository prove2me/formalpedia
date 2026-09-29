-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u245104640_246415360_r148111360_153681920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T10:57:30.644993+00:00
-- url     : https://prove2.me/submissions/474559af-37cd-4c33-9e27-f4b3baf7a0e9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [187/640, 47/160]`, `ρ ∈ [113/640, 469/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 245104640 245432320 148111360 149504000 ⟨⟨45293878606, 45293878612⟩, ⟨44485160770, 46105541473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 245432320 245760000 148111360 149504000 ⟨⟨45187988829, 45187988834⟩, ⟨44380261613, 45998655301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 245104640 245432320 149504000 150896640 ⟨⟨45707691006, 45707691013⟩, ⟨44898051846, 46520276640⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 245432320 245760000 149504000 150896640 ⟨⟨45600878047, 45600878053⟩, ⟨44792230929, 46412465871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 245760000 246087680 148111360 149504000 ⟨⟨45082238949, 45082238954⟩, ⟨44275500189, 45891911207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246087680 246415360 148111360 149504000 ⟨⟨44976628443, 44976628448⟩, ⟨44170875981, 45785308665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 245760000 246087680 149504000 150896640 ⟨⟨45494205917, 45494205922⟩, ⟨44686548672, 46304798113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 246087680 246415360 149504000 150896640 ⟨⟨45387674088, 45387674094⟩, ⟨44581004561, 46197272833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 245104640 245432320 150896640 152289280 ⟨⟨46121331567, 46121331573⟩, ⟨45310771341, 46934839707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 245432320 245760000 150896640 152289280 ⟨⟨46013596558, 46013596563⟩, ⟨45204029789, 46826105475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245104640 245432320 152289280 153681920 ⟨⟨46534800679, 46534800685⟩, ⟨45723319644, 47349231066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245432320 245760000 152289280 153681920 ⟨⟨46426144747, 46426144752⟩, ⟨45615658582, 47239574504⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 245760000 246087680 150896640 152289280 ⟨⟨45906003301, 45906003307⟩, ⟨45097427822, 46717515181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 246087680 246415360 150896640 152289280 ⟨⟨45798551270, 45798551275⟩, ⟨44990964921, 46609068292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245760000 246087680 152289280 153681920 ⟨⟨46317631487, 46317631492⟩, ⟨45508138023, 47130062802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 246087680 246415360 152289280 153681920 ⟨⟨46209260369, 46209260374⟩, ⟨45400757443, 47020695421⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 245104640 246415360 148111360 153681920 t = true :=
  ⟨_, (join_sr (m := 150896640) (by decide) (join_su (m := 245760000) (by decide) (join_sr (m := 149504000) (by decide) (join_su (m := 245432320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 245432320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 149504000) (by decide) (join_su (m := 246087680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 246087680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 245760000) (by decide) (join_sr (m := 152289280) (by decide) (join_su (m := 245432320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 245432320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 152289280) (by decide) (join_su (m := 246087680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 246087680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (187/640 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((245104640 : ℤ) : ℝ) / (D : ℝ)) = (187/640 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_165150720_r125173760_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:30:30.221951+00:00
-- url     : https://prove2.me/submissions/1cb3d9c7-389f-472d-ada6-71ec3ed9f5d7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 63/320]`, `ρ ∈ [191/1280, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 162529280 163184640 125173760 126648320 ⟨⟨66892356351, 66892356357⟩, ⟨65027118509, 68771914542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 162529280 163184640 126648320 128122880 ⟨⟨67631596878, 67631596885⟩, ⟨65763765672, 69513744827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 163184640 163840000 125173760 126648320 ⟨⟨66603402655, 66603402662⟩, ⟨64743821717, 68477228117⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163184640 163840000 126648320 128122880 ⟨⟨67339781498, 67339781505⟩, ⟨65477613937, 69216190169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 162529280 163184640 128122880 129597440 ⟨⟨68369932070, 68369932076⟩, ⟨66499513293, 70254663935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 162529280 163184640 129597440 131072000 ⟨⟨69107365498, 69107365506⟩, ⟨67234364919, 70994675472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 163184640 163840000 128122880 129597440 ⟨⟨68075265173, 68075265180⟩, ⟨66210516695, 69954251302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 163184640 163840000 129597440 131072000 ⟨⟨68809857198, 68809857206⟩, ⟨66942533483, 70691415062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 163840000 164495360 125173760 126648320 ⟨⟨66315860447, 66315860455⟩, ⟨64461897251, 68183993045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 163840000 164495360 126648320 128122880 ⟨⟨67049387897, 67049387904⟩, ⟨65192844821, 68920097148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 164495360 165150720 125173760 126648320 ⟨⟨66029716256, 66029716264⟩, ⟨64181332050, 67892195433⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 164495360 165150720 126648320 128122880 ⟨⟨66760402532, 66760402539⟩, ⟨64909445192, 68625451803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 163840000 164495360 128122880 129597440 ⟨⟨67782030237, 67782030245⟩, ⟨65922912901, 69655310479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 163840000 164495360 129597440 131072000 ⟨⟨68513790928, 68513790934⟩, ⟨66652104926, 70389636523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 164495360 165150720 128122880 129597440 ⟨⟨67490213644, 67490213651⟩, ⟨65636688706, 69357827431⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 164495360 165150720 129597440 131072000 ⟨⟨68219153001, 68219153007⟩, ⟨66363065971, 70089325754⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 165150720 125173760 131072000 t = true :=
  ⟨_, (join_su (m := 163840000) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 163184640) (by decide) (join_sr (m := 126648320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 126648320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 163184640) (by decide) (join_sr (m := 129597440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 129597440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 128122880) (by decide) (join_su (m := 164495360) (by decide) (join_sr (m := 126648320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 126648320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 164495360) (by decide) (join_sr (m := 129597440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 129597440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (63/320 : ℝ) →
    rho ∈ Set.Icc (191/1280 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e2 : (((125173760 : ℤ) : ℝ) / (D : ℝ)) = (191/1280 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

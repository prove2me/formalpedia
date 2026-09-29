-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_165150720_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:40:19.389827+00:00
-- url     : https://prove2.me/submissions/97b05184-9016-4ce9-a0a6-9a6effe1eb5f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 63/320]`, `ρ ∈ [5/32, 109/640]` by 17 cells of the computing
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
theorem cell0 : cellOK 162529280 163184640 131072000 134021120 ⟨⟨70211832615, 70211832623⟩, ⟨67884445810, 72561541840⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 163184640 163840000 131072000 134021120 ⟨⟨69910081047, 69910081053⟩, ⟨67590602139, 72251752897⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 162529280 163184640 134021120 136970240 ⟨⟨71681332323, 71681332331⟩, ⟨69348169177, 74036792254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163184640 163840000 134021120 136970240 ⟨⟨71373957936, 71373957944⟩, ⟨69048717864, 73721366032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 163840000 164495360 131072000 134021120 ⟨⟨69609786407, 69609786414⟩, ⟨67298162961, 71943474509⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 164495360 165150720 131072000 132546560 ⟨⟨68947223993, 68947223999⟩, ⟨67088580355, 70819950186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 164495360 165150720 132546560 134021120 ⟨⟨69674429996, 69674430004⟩, ⟨67813235206, 71549704133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 163840000 164495360 134021120 136970240 ⟨⟨71068059968, 71068059974⟩, ⟨68750690567, 73407469810⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 164495360 165150720 134021120 136970240 ⟨⟨70763624495, 70763624502⟩, ⟨68454073910, 73095089103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 162529280 163184640 136970240 139919360 ⟨⟨73147288458, 73147288464⟩, ⟨70808379027, 75508468838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 163184640 163840000 136970240 139919360 ⟨⟨72834330705, 72834330711⟩, ⟨70503359086, 75187445230⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 162529280 163184640 139919360 142868480 ⟨⟨74609728799, 74609728805⟩, ⟨72265102830, 76976599692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 163184640 163840000 139919360 142868480 ⟨⟨74291226699, 74291226706⟩, ⟨71954552845, 76650018151⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 163840000 164495360 136970240 139919360 ⟨⟨72522868434, 72522868440⟩, ⟨70199782262, 74867970634⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 164495360 165150720 136970240 139919360 ⟨⟨72212887594, 72212887601⟩, ⟨69897635050, 74550030444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 163840000 164495360 139919360 142868480 ⟨⟨73974238725, 73974238733⟩, ⟨71645464668, 76325004211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 164495360 165150720 139919360 142868480 ⟨⟨73658750707, 73658750715⟩, ⟨71337824668, 76001543147⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 165150720 131072000 142868480 t = true :=
  ⟨_, (join_sr (m := 136970240) (by decide) (join_su (m := 163840000) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 163184640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 163184640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 134021120) (by decide) (join_su (m := 164495360) (by decide) (leaf_ok cell4) (join_sr (m := 132546560) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 164495360) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_su (m := 163840000) (by decide) (join_sr (m := 139919360) (by decide) (join_su (m := 163184640) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 163184640) (by decide) (leaf_ok cell11) (leaf_ok cell12))) (join_sr (m := 139919360) (by decide) (join_su (m := 164495360) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_su (m := 164495360) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (63/320 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

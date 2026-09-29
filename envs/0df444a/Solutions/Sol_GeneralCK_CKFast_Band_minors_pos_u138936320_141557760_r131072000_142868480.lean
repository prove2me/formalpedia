-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u138936320_141557760_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:27:21.295155+00:00
-- url     : https://prove2.me/submissions/e6847df1-9244-4d34-a15e-5e656bb9760d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [53/320, 27/160]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 138936320 139591680 131072000 134021120 ⟨⟨82177534452, 82177534455⟩, ⟨79525200133, 84857794048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 139591680 140247040 131072000 134021120 ⟨⟨81812456329, 81812456338⟩, ⟨79170358957, 84482294274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 138936320 139591680 134021120 136970240 ⟨⟨83863633012, 83863633016⟩, ⟨81205020137, 86550109374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 139591680 140247040 134021120 136970240 ⟨⟨83492133984, 83492133991⟩, ⟨80843770123, 86168177970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 140247040 140902400 131072000 134021120 ⟨⟨81449472435, 81449472444⟩, ⟨78817533443, 84108969221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 140902400 141557760 131072000 134021120 ⟨⟨81088560525, 81088560532⟩, ⟨78466702280, 83737795686⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 140247040 140902400 134021120 136970240 ⟨⟨83122754095, 83122754103⟩, ⟨80484560838, 85788446022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 140902400 141557760 134021120 136970240 ⟨⟨82755470936, 82755470944⟩, ⟨80127370804, 85410890162⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 138936320 139591680 136970240 139919360 ⟨⟨85544435558, 85544435560⟩, ⟨82879594347, 88237078291⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 139591680 140247040 136970240 139919360 ⟨⟨85166574423, 85166574430⟩, ⟨82511993602, 87848774750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 138936320 139591680 139919360 142868480 ⟨⟨87219991330, 87219991334⟩, ⟨84548971329, 89918750723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 139591680 140247040 139919360 142868480 ⟨⟨86835826102, 86835826111⟩, ⟨84175077189, 89524133736⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 140247040 140902400 136970240 139919360 ⟨⟨84790856678, 84790856685⟩, ⟨82146458002, 87462694726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 140902400 141557760 136970240 139919360 ⟨⟨84417259752, 84417259759⟩, ⟨81782965902, 87078814694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 140247040 140902400 139919360 142868480 ⟨⟨86453827864, 86453827873⟩, ⟨83803271966, 89131763664⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 140902400 141557760 139919360 142868480 ⟨⟨86073973892, 86073973901⟩, ⟨83433533861, 88741616843⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 138936320 141557760 131072000 142868480 t = true :=
  ⟨_, (join_sr (m := 136970240) (by decide) (join_su (m := 140247040) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 139591680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 139591680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 134021120) (by decide) (join_su (m := 140902400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 140902400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 140247040) (by decide) (join_sr (m := 139919360) (by decide) (join_su (m := 139591680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 139591680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 139919360) (by decide) (join_su (m := 140902400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 140902400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (53/320 : ℝ) (27/160 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((138936320 : ℤ) : ℝ) / (D : ℝ)) = (53/320 : ℝ) := by norm_num [D]
  have e1 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

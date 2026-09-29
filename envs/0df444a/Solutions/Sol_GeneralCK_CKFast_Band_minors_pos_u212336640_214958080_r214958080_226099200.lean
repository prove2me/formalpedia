-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u212336640_214958080_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:05:55.715077+00:00
-- url     : https://prove2.me/submissions/038e9a3b-2ed9-47bb-96c3-1cec3b4cd6b2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [81/320, 41/160]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 212336640 212992000 214958080 217743360 ⟨⟨81051367693, 81051367700⟩, ⟨79113937161, 83003406229⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 212992000 213647360 214958080 217743360 ⟨⟨80709978607, 80709978613⟩, ⟨78777802809, 82656702617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212336640 212992000 217743360 220528640 ⟨⟨82043689961, 82043689968⟩, ⟨80102142208, 83999848694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212992000 213647360 217743360 220528640 ⟨⟨81698516547, 81698516554⟩, ⟨79762232980, 83649351512⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 213647360 214302720 214958080 217743360 ⟨⟨80369610355, 80369610361⟩, ⟨78442664075, 82311045443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 214302720 214958080 214958080 217743360 ⟨⟨80030255382, 80030255386⟩, ⟨78108513601, 81966426952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 213647360 214302720 217743360 220528640 ⟨⟨81354370753, 81354370761⟩, ⟨79423326176, 83299907532⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 214302720 214958080 217743360 220528640 ⟨⟨81011244995, 81011244997⟩, ⟨79085414402, 82951508970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 212336640 212992000 220528640 223313920 ⟨⟨83034892882, 83034892889⟩, ⟨81089234017, 84995165617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 212992000 213647360 220528640 223313920 ⟨⟨82685947894, 82685947900⟩, ⟨80745562550, 84640887733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 212336640 212992000 223313920 226099200 ⟨⟨84024982530, 84024982535⟩, ⟨82075218619, 85989363108⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 212992000 213647360 223313920 226099200 ⟨⟨83672278627, 83672278635⟩, ⟨81727797465, 85631317297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 213647360 214302720 220528640 223313920 ⟨⟨82338037190, 82338037197⟩, ⟨80402900193, 84287669693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 214302720 214958080 220528640 223313920 ⟨⟨81991153154, 81991153158⟩, ⟨80061239520, 83935503683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 213647360 214302720 223313920 226099200 ⟨⟨83320615557, 83320615563⟩, ⟨81381391986, 85274337854⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 214302720 214958080 223313920 226099200 ⟨⟨82969985670, 82969985674⟩, ⟨81035994727, 84918416933⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 212336640 214958080 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 213647360) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 212992000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 212992000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 217743360) (by decide) (join_su (m := 214302720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 214302720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 213647360) (by decide) (join_sr (m := 223313920) (by decide) (join_su (m := 212992000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 212992000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 223313920) (by decide) (join_su (m := 214302720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 214302720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (81/320 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

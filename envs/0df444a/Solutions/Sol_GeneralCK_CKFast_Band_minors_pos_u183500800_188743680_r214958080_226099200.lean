-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u183500800_188743680_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:18:42.359975+00:00
-- url     : https://prove2.me/submissions/2ac41f45-6cb7-4839-b797-163cb3a6c059

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/32, 9/40]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 183500800 184811520 214958080 217743360 ⟨⟨97013295290, 97013295297⟩, ⟨93390903912, 100683193358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 183500800 184811520 217743360 220528640 ⟨⟨98177282210, 98177282218⟩, ⟨94546678920, 101855388832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 184811520 186122240 214958080 217743360 ⟨⟨96226284597, 96226284604⟩, ⟨92622826028, 99876868676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 184811520 186122240 217743360 220528640 ⟨⟨97382057419, 97382057427⟩, ⟨93770414198, 101040824633⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 183500800 184811520 220528640 223313920 ⟨⟨99339460942, 99339460948⟩, ⟨95700664568, 103025756882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 183500800 184811520 223313920 226099200 ⟨⟨100499842886, 100499842894⟩, ⟨96852872119, 104194309048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 184811520 186122240 220528640 223313920 ⟨⟨98536060243, 98536060251⟩, ⟨94916250624, 102202991932⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 184811520 186122240 223313920 226099200 ⟨⟨99688304150, 99688304158⟩, ⟨96060346256, 103363381790⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 186122240 187432960 214958080 217743360 ⟨⟨95444933451, 95444933455⟩, ⟨91860192912, 99076423848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 186122240 187432960 217743360 220528640 ⟨⟨96592524897, 96592524899⟩, ⟨92999627310, 100232172607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 187432960 188743680 214958080 217743360 ⟨⟨94669152499, 94669152507⟩, ⟨91102918886, 98281765750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 187432960 188743680 217743360 220528640 ⟨⟨95808595026, 95808595034⟩, ⟨92234232300, 99429339389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 186122240 187432960 220528640 223313920 ⟨⟨97738383829, 97738383833⟩, ⟨94137346890, 101386170762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 186122240 187432960 223313920 226099200 ⟨⟨98882521018, 98882521022⟩, ⟨95273362290, 102538429211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 187432960 188743680 220528640 223313920 ⟨⟨96946341834, 96946341842⟩, ⟨93363867138, 100575199775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 187432960 188743680 223313920 226099200 ⟨⟨98082403389, 98082403395⟩, ⟨94491833746, 101719357493⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 183500800 188743680 214958080 226099200 t = true :=
  ⟨_, (join_su (m := 186122240) (by decide) (join_sr (m := 220528640) (by decide) (join_su (m := 184811520) (by decide) (join_sr (m := 217743360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 217743360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 184811520) (by decide) (join_sr (m := 223313920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 223313920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 220528640) (by decide) (join_su (m := 187432960) (by decide) (join_sr (m := 217743360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 217743360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 187432960) (by decide) (join_sr (m := 223313920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 223313920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/32 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

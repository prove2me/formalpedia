-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_167772160_r367001600_390594560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:06:41.862236+00:00
-- url     : https://prove2.me/submissions/0a1294ae-b5a8-475f-9f0d-78c20412a12e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 1/5]`, `ρ ∈ [7/16, 149/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 159907840 367001600 372899840 ⟨⟨183461680995, 183461681003⟩, ⟨174454182849, 192685441789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157286400 159907840 372899840 378798080 ⟨⟨186016035187, 186016035197⟩, ⟨176977724477, 195269944256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 159907840 162529280 367001600 372899840 ⟨⟨180790531024, 180790531033⟩, ⟨171879359262, 189915190409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 159907840 162529280 372899840 378798080 ⟨⟨183317163474, 183317163484⟩, ⟨174375050546, 192472154474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 157286400 159907840 378798080 384696320 ⟨⟨188562277435, 188562277443⟩, ⟨179493331777, 197846151114⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 157286400 159907840 384696320 390594560 ⟨⟨191100529775, 191100529785⟩, ⟨182001123500, 200414187743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 159907840 162529280 378798080 384696320 ⟨⟨185835964731, 185835964740⟩, ⟨176863081117, 195021110680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 159907840 162529280 384696320 390594560 ⟨⟨188347051205, 188347051213⟩, ⟨179343564294, 197562178579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 162529280 165150720 367001600 372899840 ⟨⟨178153765886, 178153765891⟩, ⟨169336968021, 187181335977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 162529280 165150720 372899840 378798080 ⟨⟨180652674050, 180652674054⟩, ⟨171804827195, 189710735892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 165150720 167772160 367001600 372899840 ⟨⟨175550394472, 175550394481⟩, ⟨166826078244, 184482825581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 165150720 167772160 372899840 378798080 ⟨⟨178021581512, 178021581521⟩, ⟨169266128140, 186984642526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 162529280 165150720 378798080 384696320 ⟨⟨183144024219, 183144024222⟩, ⟨174265291808, 192232408086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 162529280 165150720 384696320 390594560 ⟨⟨185627927411, 185627927416⟩, ⟨176718469972, 194746466535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 165150720 167772160 378798080 384696320 ⟨⟨180485476338, 180485476347⟩, ⟨171699042307, 189479004405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 165150720 167772160 384696320 390594560 ⟨⟨182942184810, 182942184820⟩, ⟨174124923876, 191966019854⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 167772160 367001600 390594560 t = true :=
  ⟨_, (join_su (m := 162529280) (by decide) (join_sr (m := 378798080) (by decide) (join_su (m := 159907840) (by decide) (join_sr (m := 372899840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 372899840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 159907840) (by decide) (join_sr (m := 384696320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 384696320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 378798080) (by decide) (join_su (m := 165150720) (by decide) (join_sr (m := 372899840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 372899840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 165150720) (by decide) (join_sr (m := 384696320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 384696320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (7/16 : ℝ) (149/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((367001600 : ℤ) : ℝ) / (D : ℝ)) = (7/16 : ℝ) := by norm_num [D]
  have e3 : (((390594560 : ℤ) : ℝ) / (D : ℝ)) = (149/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

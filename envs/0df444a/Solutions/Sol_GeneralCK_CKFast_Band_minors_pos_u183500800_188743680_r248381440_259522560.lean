-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u183500800_188743680_r248381440_259522560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:18:51.505473+00:00
-- url     : https://prove2.me/submissions/131a04db-d3d8-4c92-a0d0-b00912e65433

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/32, 9/40]`, `ρ ∈ [379/1280, 99/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 183500800 184811520 248381440 251166720 ⟨⟨110864269415, 110864269423⟩, ⟨107144548073, 114631430506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 183500800 184811520 251166720 253952000 ⟨⟨112007294281, 112007294289⟩, ⟨108279578142, 115782442000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 184811520 186122240 248381440 251166720 ⟨⟨109981140786, 109981140793⟩, ⟨106280642789, 113728719756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 184811520 186122240 251166720 253952000 ⟨⟨111116389246, 111116389252⟩, ⟨107407917203, 114871935994⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 183500800 184811520 253952000 256737280 ⟨⟨113148642929, 113148642937⟩, ⟨109412949248, 116931759634⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 183500800 184811520 256737280 259522560 ⟨⟨114288325898, 114288325905⟩, ⟨110544671802, 118079394070⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 184811520 186122240 253952000 256737280 ⟨⟨112249996008, 112249996015⟩, ⟨108533566665, 116013493404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 184811520 186122240 256737280 259522560 ⟨⟨113381971324, 113381971330⟩, ⟨109657601305, 117153402356⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 186122240 187432960 248381440 251166720 ⟨⟨109104019744, 109104019747⟩, ⟨105422535191, 112832231399⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 186122240 187432960 251166720 253952000 ⟨⟨110231516623, 110231516627⟩, ⟨106542079248, 113967676681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 187432960 188743680 248381440 251166720 ⟨⟨108232814573, 108232814580⟩, ⟨104570137027, 111941870174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 187432960 188743680 251166720 253952000 ⟨⟨109352584571, 109352584579⟩, ⟨105681975881, 113069568698⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 186122240 187432960 253952000 256737280 ⟨⟨111357405719, 111357405723⟩, ⟨107660031769, 115101497554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 186122240 187432960 256737280 259522560 ⟨⟨112481697003, 112481697007⟩, ⟨108776402606, 116233704103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 187432960 188743680 253952000 256737280 ⟨⟨110470780105, 110470780113⟩, ⟨106792256025, 114195676625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 187432960 188743680 256737280 259522560 ⟨⟨111587410871, 111587410879⟩, ⟨107900987048, 115320203761⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 183500800 188743680 248381440 259522560 t = true :=
  ⟨_, (join_su (m := 186122240) (by decide) (join_sr (m := 253952000) (by decide) (join_su (m := 184811520) (by decide) (join_sr (m := 251166720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 251166720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 184811520) (by decide) (join_sr (m := 256737280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 256737280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 253952000) (by decide) (join_su (m := 187432960) (by decide) (join_sr (m := 251166720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 251166720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 187432960) (by decide) (join_sr (m := 256737280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 256737280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/32 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (379/1280 : ℝ) (99/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  have e3 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

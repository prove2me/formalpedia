-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_199229440_r749731840_794296320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:11:04.54801+00:00
-- url     : https://prove2.me/submissions/75c2f84e-decd-4c56-a0a7-409e9b44dd0c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 19/80]`, `ρ ∈ [143/160, 303/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 191365120 749731840 760872960 ⟨⟨290335446147, 290335446151⟩, ⟨278983803311, 301908424962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 191365120 193986560 749731840 760872960 ⟨⟨286525795888, 286525795898⟩, ⟨275270662378, 298001991725⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 188743680 191365120 760872960 772014080 ⟨⟨294110708785, 294110708792⟩, ⟨282705543048, 305735581409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 191365120 193986560 760872960 772014080 ⟨⟨290264021437, 290264021447⟩, ⟨278955012872, 301792558586⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 193986560 196608000 749731840 760872960 ⟨⟨282735738088, 282735738098⟩, ⟨271576393138, 294115831367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 196608000 199229440 749731840 760872960 ⟨⟨278964863367, 278964863377⟩, ⟨267900595569, 290249526618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 193986560 196608000 760872960 772014080 ⟨⟨286436652516, 286436652526⟩, ⟨275223111060, 297869501698⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 196608000 199229440 760872960 772014080 ⟨⟨282628200137, 282628200147⟩, ⟨271509444322, 293966001757⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 188743680 191365120 772014080 783155200 ⟨⟨297879355724, 297879355731⟩, ⟨286420795992, 309555966713⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 191365120 193986560 772014080 783155200 ⟨⟨293995836250, 293995836260⟩, ⟨282633075322, 305576565578⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 188743680 191365120 783155200 794296320 ⟨⟨301641644338, 301641644345⟩, ⟨290129813054, 313369844412⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 191365120 193986560 783155200 794296320 ⟨⟨297721488515, 297721488527⟩, ⟨286305091715, 309354266808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 193986560 196608000 772014080 783155200 ⟨⟨290131357917, 290131357927⟩, ⟨278863736321, 301616820343⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 196608000 199229440 772014080 783155200 ⟨⟨286285526278, 286285526289⟩, ⟨275112392397, 297676330206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 193986560 196608000 783155200 794296320 ⟨⟨293820093521, 293820093532⟩, ⟨282498502207, 305358032191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 196608000 199229440 783155200 794296320 ⟨⟨289937072282, 289937072292⟩, ⟨278709664597, 301380747874⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 199229440 749731840 794296320 t = true :=
  ⟨_, (join_sr (m := 772014080) (by decide) (join_su (m := 193986560) (by decide) (join_sr (m := 760872960) (by decide) (join_su (m := 191365120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 191365120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 760872960) (by decide) (join_su (m := 196608000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 196608000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 193986560) (by decide) (join_sr (m := 783155200) (by decide) (join_su (m := 191365120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 191365120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 783155200) (by decide) (join_su (m := 196608000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 196608000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (143/160 : ℝ) (303/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((749731840 : ℤ) : ℝ) / (D : ℝ)) = (143/160 : ℝ) := by norm_num [D]
  have e3 : (((794296320 : ℤ) : ℝ) / (D : ℝ)) = (303/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

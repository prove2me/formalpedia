-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_193986560_r326369280_348651520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:41:36.706557+00:00
-- url     : https://prove2.me/submissions/0d2f33ac-7a8a-4b1b-823a-fc89e3305a8d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 37/160]`, `ρ ∈ [249/640, 133/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 190054400 326369280 331939840 ⟨⟨138488619856, 138488619863⟩, ⟨133878090755, 143165741246⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 190054400 191365120 326369280 331939840 ⟨⟨137421910858, 137421910865⟩, ⟨132837236923, 142072686389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 188743680 190054400 331939840 337510400 ⟨⟨140630595263, 140630595271⟩, ⟨136003880880, 145323811929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 190054400 191365120 331939840 337510400 ⟨⟨139550200645, 139550200654⟩, ⟨134949363994, 144217054780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 191365120 192675840 326369280 331939840 ⟨⟨136361344869, 136361344877⟩, ⟨131802286169, 140986019947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 192675840 193986560 326369280 331939840 ⟨⟨135306835974, 135306835979⟩, ⟨130773156088, 139905652418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 191365120 192675840 331939840 337510400 ⟨⟨138475969684, 138475969691⟩, ⟨133900772419, 143116704970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 192675840 193986560 331939840 337510400 ⟨⟨137407816599, 137407816603⟩, ⟨132858023834, 142022673178⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 188743680 190054400 337510400 343080960 ⟨⟨142767426825, 142767426832⟩, ⟨138124592007, 147476672321⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 190054400 191365120 337510400 343080960 ⟨⟨141673448098, 141673448105⟩, ⟨137056511814, 146356316168⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 188743680 190054400 343080960 348651520 ⟨⟨144899177774, 144899177782⟩, ⟨140240286417, 149624386618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 190054400 191365120 343080960 348651520 ⟨⟨143791714840, 143791714848⟩, ⟨139158741090, 148490533100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 191365120 192675840 337510400 343080960 ⟨⟨140585652078, 140585652087⟩, ⟨135994377594, 145242384651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 192675840 193986560 337510400 343080960 ⟨⟨139503953147, 139503953151⟩, ⟨134938107136, 144134788663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 191365120 192675840 343080960 348651520 ⟨⟨142690452111, 142690452120⟩, ⟨138083160866, 147363119940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 192675840 193986560 343080960 348651520 ⟨⟨141595304140, 141595304146⟩, ⟨137013463660, 146242058255⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 193986560 326369280 348651520 t = true :=
  ⟨_, (join_sr (m := 337510400) (by decide) (join_su (m := 191365120) (by decide) (join_sr (m := 331939840) (by decide) (join_su (m := 190054400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 190054400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 331939840) (by decide) (join_su (m := 192675840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 192675840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 191365120) (by decide) (join_sr (m := 343080960) (by decide) (join_su (m := 190054400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 190054400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 343080960) (by decide) (join_su (m := 192675840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 192675840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (37/160 : ℝ) →
    rho ∈ Set.Icc (249/640 : ℝ) (133/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e2 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  have e3 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

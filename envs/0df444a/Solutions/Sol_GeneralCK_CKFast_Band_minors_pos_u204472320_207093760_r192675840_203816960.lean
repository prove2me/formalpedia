-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_207093760_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:18:33.525263+00:00
-- url     : https://prove2.me/submissions/61b185a0-68a8-48af-a0f2-63b67484baa1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 79/320]`, `ρ ∈ [147/640, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 204472320 205127680 192675840 195461120 ⟨⟨76877261772, 76877261775⟩, ⟨74908844760, 78861030782⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 205127680 205783040 192675840 195461120 ⟨⟨76554481925, 76554481933⟩, ⟨74591559903, 78532689235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 204472320 205127680 195461120 198246400 ⟨⟨77926059960, 77926059963⟩, ⟨75953351522, 79914121389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205127680 205783040 195461120 198246400 ⟨⟨77599293667, 77599293673⟩, ⟨75632090477, 79581783378⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 205783040 206438400 192675840 195461120 ⟨⟨76232756562, 76232756568⟩, ⟨74275301654, 78205430504⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 206438400 207093760 192675840 195461120 ⟨⟨75912077581, 75912077588⟩, ⟨73960062139, 77879246262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 205783040 206438400 195461120 198246400 ⟨⟨77273590157, 77273590164⟩, ⟨75311864356, 79250536466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 206438400 207093760 195461120 198246400 ⟨⟨76948941289, 76948941296⟩, ⟨74992665242, 78920372286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 205127680 198246400 201031680 ⟨⟨78973516585, 78973516588⟩, ⟨76996524712, 80965862343⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 205127680 205783040 198246400 201031680 ⟨⟨78642779000, 78642779006⟩, ⟨76671302495, 80629543164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 204472320 205127680 201031680 203816960 ⟨⟨80019639216, 80019639219⟩, ⟨78038371845, 82016261265⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 205127680 205783040 201031680 203816960 ⟨⟨79684945383, 79684945389⟩, ⟨77709203362, 81675976104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 205783040 206438400 198246400 201031680 ⟨⟨78313112354, 78313112360⟩, ⟨76347123374, 80294323222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 206438400 207093760 198246400 201031680 ⟨⟨77984508464, 77984508470⟩, ⟨76023979389, 79960194105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 205783040 206438400 201031680 203816960 ⟨⟨79351330500, 79351330507⟩, ⟨77381086001, 81336798166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 206438400 207093760 201031680 203816960 ⟨⟨79018786343, 79018786350⟩, ⟨77054011768, 80998719004⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 207093760 192675840 203816960 t = true :=
  ⟨_, (join_sr (m := 198246400) (by decide) (join_su (m := 205783040) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 205127680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 205127680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 195461120) (by decide) (join_su (m := 206438400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 206438400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 205783040) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 205127680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 205127680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 201031680) (by decide) (join_su (m := 206438400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 206438400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (79/320 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((207093760 : ℤ) : ℝ) / (D : ℝ)) = (79/320 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

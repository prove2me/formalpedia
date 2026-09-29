-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_235929600_r348651520_359792640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:50:07.619883+00:00
-- url     : https://prove2.me/submissions/87fab415-7650-4493-9acd-ba30e455d3c8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 9/32]`, `ρ ∈ [133/320, 549/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231997440 348651520 351436800 ⟨⟨113437218641, 113437218649⟩, ⟨110046726246, 116865953154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 231997440 351436800 354222080 ⟨⟨114290048682, 114290048690⟩, ⟨110892636499, 117725731474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231997440 233308160 348651520 351436800 ⟨⟨112482152043, 112482152046⟩, ⟨109105988498, 115896359458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231997440 233308160 351436800 354222080 ⟨⟨113328584241, 113328584245⟩, ⟨109945522619, 116749719101⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 231997440 354222080 357007360 ⟨⟨115142252147, 115142252153⟩, ⟨111737923435, 118584879744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230686720 231997440 357007360 359792640 ⟨⟨115993832311, 115993832319⟩, ⟨112582590314, 119443401265⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231997440 233308160 354222080 357007360 ⟨⟨114174404157, 114174404160⟩, ⟨110784447519, 117602463192⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 231997440 233308160 357007360 359792640 ⟨⟨115019614978, 115019614980⟩, ⟨111622766368, 118454594938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 234618880 348651520 351436800 ⟨⟨111531132272, 111531132280⟩, ⟨108169182475, 114930929633⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 233308160 234618880 351436800 354222080 ⟨⟨112371175350, 112371175356⟩, ⟨109002349444, 115777879040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 234618880 235929600 348651520 351436800 ⟨⟨110584106646, 110584106654⟩, ⟨107236256927, 113969609525⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 234618880 235929600 351436800 354222080 ⟨⟨111417769308, 111417769314⟩, ⟨108063065700, 114810157127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 233308160 234618880 354222080 357007360 ⟨⟨113210620190, 113210620197⟩, ⟨109834921044, 116624227141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 233308160 234618880 357007360 359792640 ⟨⟨114049469895, 114049469902⟩, ⟨110666900357, 117469977052⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 234618880 235929600 354222080 357007360 ⟨⟨112250847534, 112250847542⟩, ⟨108889292717, 115650117421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 234618880 235929600 357007360 359792640 ⟨⟨113083344342, 113083344350⟩, ⟨109714940974, 116489493439⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 235929600 348651520 359792640 t = true :=
  ⟨_, (join_su (m := 233308160) (by decide) (join_sr (m := 354222080) (by decide) (join_su (m := 231997440) (by decide) (join_sr (m := 351436800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 351436800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 231997440) (by decide) (join_sr (m := 357007360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 357007360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 354222080) (by decide) (join_su (m := 234618880) (by decide) (join_sr (m := 351436800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 351436800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 234618880) (by decide) (join_sr (m := 357007360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 357007360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (133/320 : ℝ) (549/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  have e3 : (((359792640 : ℤ) : ℝ) / (D : ℝ)) = (549/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

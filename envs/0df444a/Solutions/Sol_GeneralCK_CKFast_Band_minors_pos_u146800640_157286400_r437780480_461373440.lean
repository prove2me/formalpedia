-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_157286400_r437780480_461373440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:06:56.539041+00:00
-- url     : https://prove2.me/submissions/e4b9f1bc-3b22-404a-afa1-e5a9801b8771

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 3/16]`, `ρ ∈ [167/320, 11/20]` by 15 cells of the computing
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
theorem cell0 : cellOK 146800640 149422080 437780480 443678720 ⟨⟨225908927045, 225908927054⟩, ⟨216147286282, 235887316191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 146800640 149422080 443678720 449576960 ⟨⟨228471477585, 228471477595⟩, ⟨218681996246, 238476739588⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 149422080 152043520 437780480 443678720 ⟨⟨222777013321, 222777013324⟩, ⟨213117036705, 232651476076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 149422080 152043520 443678720 449576960 ⟨⟨225315256827, 225315256831⟩, ⟨215627141063, 235216953013⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 146800640 149422080 449576960 461373440 ⟨⟨232300922543, 232300922553⟩, ⟨220341992924, 244579149883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 149422080 152043520 449576960 455475200 ⟨⟨227846051306, 227846051311⟩, ⟨218129953618, 237774818837⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 149422080 152043520 455475200 461373440 ⟨⟨230369514040, 230369514045⟩, ⟨220625588573, 240325193943⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 152043520 154664960 437780480 443678720 ⟨⟨219683008621, 219683008629⟩, ⟨210122786832, 229455488454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 152043520 154664960 443678720 449576960 ⟨⟨222196834376, 222196834385⟩, ⟨212608200637, 231996880035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 154664960 157286400 437780480 443678720 ⟨⟨216625857051, 216625857061⟩, ⟨207163536496, 226298241351⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 154664960 157286400 443678720 449576960 ⟨⟨219115163028, 219115163038⟩, ⟨209624182288, 228815418672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 152043520 154664960 449576960 455475200 ⟨⟨224703447040, 224703447050⟩, ⟨215086553539, 234530901212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 152043520 154664960 455475200 461373440 ⟨⟨227202958963, 227202958973⟩, ⟨217557954965, 237057667285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 154664960 157286400 449576960 455475200 ⟨⟨221597486617, 221597486627⟩, ⟨212077992800, 231325461142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 154664960 157286400 455475200 461373440 ⟨⟨224072935419, 224072935427⟩, ⟨214525072863, 233828479161⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 157286400 437780480 461373440 t = true :=
  ⟨_, (join_su (m := 152043520) (by decide) (join_sr (m := 449576960) (by decide) (join_su (m := 149422080) (by decide) (join_sr (m := 443678720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 443678720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 149422080) (by decide) (leaf_ok cell4) (join_sr (m := 455475200) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 449576960) (by decide) (join_su (m := 154664960) (by decide) (join_sr (m := 443678720) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 443678720) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 154664960) (by decide) (join_sr (m := 455475200) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 455475200) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (167/320 : ℝ) (11/20 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  have e3 : (((461373440 : ℤ) : ℝ) / (D : ℝ)) = (11/20 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

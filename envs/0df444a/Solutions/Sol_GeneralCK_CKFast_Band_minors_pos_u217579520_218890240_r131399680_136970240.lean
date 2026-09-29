-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u217579520_218890240_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:22:03.753323+00:00
-- url     : https://prove2.me/submissions/04e63ee4-a35c-4f74-85ea-b8afa129a035

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [83/320, 167/640]`, `ρ ∈ [401/2560, 209/1280]` by 14 cells of the computing
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
theorem cell0 : cellOK 217579520 217907200 131399680 132792320 ⟨⟨48783548380, 48783548387⟩, ⟨47895611941, 49674979549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 217907200 218234880 131399680 132792320 ⟨⟨48676092935, 48676092941⟩, ⟨47789342148, 49566330676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 217579520 217907200 132792320 134184960 ⟨⟨49282116600, 49282116607⟩, ⟨48393124716, 50174604097⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 217907200 218234880 132792320 134184960 ⟨⟨49173626679, 49173626685⟩, ⟨48285822086, 50064919116⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 218234880 218562560 131399680 132792320 ⟨⟨48568814865, 48568814871⟩, ⟨47683246762, 49457862173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 218562560 218890240 131399680 132792320 ⟨⟨48461713472, 48461713473⟩, ⟨47577325100, 49349573324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 218234880 218562560 132792320 134184960 ⟨⟨49065315458, 49065315464⟩, ⟨48178695188, 49955415835⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 218562560 218890240 132792320 134184960 ⟨⟨48957182235, 48957182239⟩, ⟨48071743334, 49846093529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 217579520 217907200 134184960 135577600 ⟨⟨49780383805, 49780383812⟩, ⟨48890337267, 50673926831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 217907200 218234880 134184960 135577600 ⟨⟨49670861237, 49670861242⟩, ⟨48782003623, 50563207581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 218234880 135577600 136970240 ⟨⟨50223051382, 50223051385⟩, ⟨48729258113, 51726401875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 218234880 218562560 134184960 135577600 ⟨⟨49561518686, 49561518692⟩, ⟨48673847025, 50452671349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 218562560 218890240 134184960 135577600 ⟨⟨49452355444, 49452355448⟩, ⟨48565866782, 50342317406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 218234880 218890240 135577600 136970240 ⟨⟨50002307067, 50002307072⟩, ⟨48511869621, 51502265378⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 217579520 218890240 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 218234880) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 217907200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 217907200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 218562560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 218562560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 218234880) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 217907200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 135577600) (by decide) (join_su (m := 218562560) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (83/320 : ℝ) (167/640 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e1 : (((218890240 : ℤ) : ℝ) / (D : ℝ)) = (167/640 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

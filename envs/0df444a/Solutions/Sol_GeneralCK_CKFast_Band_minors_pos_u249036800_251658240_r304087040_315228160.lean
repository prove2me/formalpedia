-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_251658240_r304087040_315228160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:44:53.613207+00:00
-- url     : https://prove2.me/submissions/e6d14c22-8bd0-4804-afdf-d8df0d9718a2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 3/10]`, `ρ ∈ [29/80, 481/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249692160 304087040 306872320 ⟨⟨88329338628, 88329338635⟩, ⟨86538374255, 90132406852⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249692160 250347520 304087040 306872320 ⟨⟨87928054727, 87928054734⟩, ⟨86141470032, 89726704014⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249036800 249692160 306872320 309657600 ⟨⟨89102471769, 89102471776⟩, ⟨87307974136, 90909082749⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249692160 250347520 306872320 309657600 ⟨⟨88697952553, 88697952560⟩, ⟨86907842620, 90500136683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 250347520 251002880 304087040 306872320 ⟨⟨87527580528, 87527580531⟩, ⟨85745358934, 89321827647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 251002880 251658240 304087040 306872320 ⟨⟨87127910594, 87127910601⟩, ⟨85350035630, 88917772217⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 250347520 251002880 306872320 309657600 ⟨⟨88294246018, 88294246021⟩, ⟨86508507223, 90092020051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 251002880 251658240 306872320 309657600 ⟨⟨87891346715, 87891346721⟩, ⟨86109962605, 89684727302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 249692160 309657600 312442880 ⟨⟨89875117963, 89875117969⟩, ⟨88077088221, 91685270502⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249692160 250347520 309657600 312442880 ⟨⟨89467369582, 89467369589⟩, ⟨87673735511, 91273087410⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 249036800 249692160 312442880 315228160 ⟨⟨90647279536, 90647279542⟩, ⟨88845718825, 92460972444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 249692160 250347520 312442880 315228160 ⟨⟨90236308104, 90236308111⟩, ⟨88439150989, 92045558488⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 250347520 251002880 309657600 312442880 ⟨⟨89060436802, 89060436805⟩, ⟨87271181858, 90861736650⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 251002880 251658240 309657600 312442880 ⟨⟨88654314161, 88654314168⟩, ⟨86869421912, 90451212664⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 250347520 251002880 312442880 315228160 ⟨⟨89826155135, 89826155138⟩, ⟨88033385088, 91630979708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251002880 251658240 312442880 315228160 ⟨⟨89416815157, 89416815164⟩, ⟨87628415762, 91217230532⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 251658240 304087040 315228160 t = true :=
  ⟨_, (join_sr (m := 309657600) (by decide) (join_su (m := 250347520) (by decide) (join_sr (m := 306872320) (by decide) (join_su (m := 249692160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 249692160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 306872320) (by decide) (join_su (m := 251002880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 251002880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 250347520) (by decide) (join_sr (m := 312442880) (by decide) (join_su (m := 249692160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 249692160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 312442880) (by decide) (join_su (m := 251002880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 251002880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (29/80 : ℝ) (481/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  have e3 : (((315228160 : ℤ) : ℝ) / (D : ℝ)) = (481/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

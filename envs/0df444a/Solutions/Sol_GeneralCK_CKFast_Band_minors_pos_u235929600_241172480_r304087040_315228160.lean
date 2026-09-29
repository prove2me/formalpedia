-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_241172480_r304087040_315228160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:36:16.220541+00:00
-- url     : https://prove2.me/submissions/f8a2033e-1c43-4b97-952c-6e5d1a868193

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 23/80]`, `ρ ∈ [29/80, 481/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 237240320 304087040 306872320 ⟨⟨96324297758, 96324297765⟩, ⟨93100091206, 99585428987⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 235929600 237240320 306872320 309657600 ⟨⟨97161129791, 97161129798⟩, ⟨93930049648, 100429169532⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 237240320 238551040 304087040 306872320 ⟨⟨95488794922, 95488794928⟩, ⟨92278076434, 98736235309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237240320 238551040 306872320 309657600 ⟨⟨96319039198, 96319039205⟩, ⟨93101472880, 99573363061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235929600 237240320 309657600 312442880 ⟨⟨97997342619, 97997342626⟩, ⟨94759391650, 101272287920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235929600 237240320 312442880 315228160 ⟨⟨98832939346, 98832939353⟩, ⟨95588120299, 102114787271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237240320 238551040 309657600 312442880 ⟨⟨97148678965, 97148678971⟩, ⟨93924267383, 100409883552⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 237240320 238551040 312442880 315228160 ⟨⟨97977717235, 97977717242⟩, ⟨94746462939, 101245799812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 239861760 304087040 306872320 ⟨⟨94656960527, 94656960531⟩, ⟨91459617481, 97890824826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 238551040 239861760 306872320 309657600 ⟨⟨95480629719, 95480629723⟩, ⟨92276464769, 98721352272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 239861760 241172480 304087040 306872320 ⟨⟨93828745460, 93828745466⟩, ⟨90644666698, 97049146940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 239861760 241172480 306872320 309657600 ⟨⟨94645852162, 94645852169⟩, ⟨91454977581, 97873086497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 238551040 239861760 309657600 312442880 ⟨⟨96303708828, 96303708833⟩, ⟨93092724347, 99551287083⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 238551040 239861760 312442880 315228160 ⟨⟨97126200781, 97126200785⟩, ⟨93908399125, 100380632201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239861760 241172480 309657600 312442880 ⟨⟨95462382944, 95462382949⟩, ⟨92264714727, 98696447776⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239861760 241172480 312442880 315228160 ⟨⟨96278340646, 96278340653⟩, ⟨93073880963, 99519233631⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 241172480 304087040 315228160 t = true :=
  ⟨_, (join_su (m := 238551040) (by decide) (join_sr (m := 309657600) (by decide) (join_su (m := 237240320) (by decide) (join_sr (m := 306872320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 306872320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 237240320) (by decide) (join_sr (m := 312442880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 312442880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 309657600) (by decide) (join_su (m := 239861760) (by decide) (join_sr (m := 306872320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 306872320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 239861760) (by decide) (join_sr (m := 312442880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 312442880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (29/80 : ℝ) (481/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  have e3 : (((315228160 : ℤ) : ℝ) / (D : ℝ)) = (481/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

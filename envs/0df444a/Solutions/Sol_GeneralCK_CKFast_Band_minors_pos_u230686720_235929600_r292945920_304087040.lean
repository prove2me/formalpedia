-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_235929600_r292945920_304087040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:13:42.654245+00:00
-- url     : https://prove2.me/submissions/42c85b10-0650-4e43-83b0-190456c0b3c6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 9/32]`, `ρ ∈ [447/1280, 29/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231997440 292945920 295731200 ⟨⟨96243877476, 96243877482⟩, ⟨92992498389, 99532884915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 231997440 295731200 298516480 ⟨⟨97109946834, 97109946842⟩, ⟨93851578263, 100405976418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231997440 233308160 292945920 295731200 ⟨⟨95419912590, 95419912593⟩, ⟨92182384759, 98694853983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231997440 233308160 295731200 298516480 ⟨⟨96279278527, 96279278530⟩, ⟨93034787125, 99561216934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 231997440 298516480 301301760 ⟨⟨97975321389, 97975321395⟩, ⟨94709967023, 101278369222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230686720 231997440 301301760 304087040 ⟨⟨98840004676, 98840004682⟩, ⟨95567668183, 102150066882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231997440 233308160 298516480 301301760 ⟨⟨97137965863, 97137965867⟩, ⟨93886514360, 100426897615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 231997440 233308160 301301760 304087040 ⟨⟨97995978038, 97995978040⟩, ⟨94737569879, 101291899481⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 234618880 292945920 295731200 ⟨⟨94599764863, 94599764869⟩, ⟨91375968886, 97860761958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 233308160 234618880 295731200 298516480 ⟨⟨95452441511, 95452441518⟩, ⟨92221708049, 98720410297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 234618880 235929600 292945920 295731200 ⟨⟨93783382671, 93783382678⟩, ⟨90573200720, 97030555599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 234618880 235929600 295731200 298516480 ⟨⟨94629384073, 94629384080⟩, ⟨91412290890, 97883503185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 233308160 234618880 298516480 301301760 ⟨⟨96304455471, 96304455478⟩, ⟨93066787776, 99579392500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 233308160 234618880 301301760 304087040 ⟨⟨97155810080, 97155810086⟩, ⟨93911211386, 100437711919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 234618880 235929600 298516480 301301760 ⟨⟨95474738410, 95474738416⟩, ⟨92250737032, 98735800472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 234618880 235929600 301301760 304087040 ⟨⟨96319448920, 96319448926⟩, ⟨93088542373, 99587450716⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 235929600 292945920 304087040 t = true :=
  ⟨_, (join_su (m := 233308160) (by decide) (join_sr (m := 298516480) (by decide) (join_su (m := 231997440) (by decide) (join_sr (m := 295731200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 295731200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 231997440) (by decide) (join_sr (m := 301301760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 301301760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 298516480) (by decide) (join_su (m := 234618880) (by decide) (join_sr (m := 295731200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 295731200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 234618880) (by decide) (join_sr (m := 301301760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 301301760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (447/1280 : ℝ) (29/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  have e3 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

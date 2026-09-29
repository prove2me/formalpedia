-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u152043520_154664960_r154664960_166461440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:39:54.504715+00:00
-- url     : https://prove2.me/submissions/24c386c8-4f9c-4a3e-815a-85457766c65f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [29/160, 59/320]`, `ρ ∈ [59/320, 127/640]` by 14 cells of the computing
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
theorem cell0 : cellOK 152043520 152698880 154664960 157614080 ⟨⟨87631112542, 87631112546⟩, ⟨85122523792, 90163953503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 152698880 153354240 154664960 157614080 ⟨⟨87257682349, 87257682358⟩, ⟨84758021751, 89781451934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 152043520 152698880 157614080 160563200 ⟨⟨89160424320, 89160424325⟩, ⟨86646113810, 91698946601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 152698880 153354240 157614080 160563200 ⟨⟨88781401376, 88781401382⟩, ⟨86276029296, 91310842939⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 153354240 154009600 154664960 157614080 ⟨⟨86886115208, 86886115215⟩, ⟨84395321182, 89400876327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 154009600 154664960 154664960 157614080 ⟨⟨86516393178, 86516393186⟩, ⟨84034404807, 89022208069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 153354240 154009600 157614080 160563200 ⟨⟨88404259341, 88404259348⟩, ⟨85907764235, 90924682961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 154009600 154664960 157614080 160563200 ⟨⟨88028980177, 88028980186⟩, ⟨85541301248, 90540447957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 152043520 152698880 160563200 163512320 ⟨⟨90685775049, 90685775055⟩, ⟨88165777296, 93229943959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 152698880 153354240 160563200 163512320 ⟨⟨90301202069, 90301202076⟩, ⟨87790152556, 92836281389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 152043520 153354240 163512320 166461440 ⟨⟨92011916696, 92011916704⟩, ⟨87972507604, 96112882357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 153354240 154009600 160563200 163512320 ⟨⟨89918527413, 89918527419⟩, ⟨87416364813, 92444579774⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 154009600 154664960 160563200 163512320 ⟨⟨89537732943, 89537732951⟩, ⟨87044396583, 92054820309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 153354240 154664960 163512320 166461440 ⟨⟨91235581136, 91235581139⟩, ⟨87221768824, 95310303657⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 152043520 154664960 154664960 166461440 t = true :=
  ⟨_, (join_sr (m := 160563200) (by decide) (join_su (m := 153354240) (by decide) (join_sr (m := 157614080) (by decide) (join_su (m := 152698880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 152698880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 157614080) (by decide) (join_su (m := 154009600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 154009600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 153354240) (by decide) (join_sr (m := 163512320) (by decide) (join_su (m := 152698880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 163512320) (by decide) (join_su (m := 154009600) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (29/160 : ℝ) (59/320 : ℝ) →
    rho ∈ Set.Icc (59/320 : ℝ) (127/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e1 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e2 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e3 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

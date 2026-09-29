-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_204472320_r304087040_326369280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:41:08.702511+00:00
-- url     : https://prove2.me/submissions/f751bd10-4317-4afb-8f6f-a1a160c2feda

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 39/160]`, `ρ ∈ [29/80, 249/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 200540160 304087040 309657600 ⟨⟨121945139250, 121945139254⟩, ⟨117599306285, 126353959409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 200540160 201850880 304087040 309657600 ⟨⟨120980236552, 120980236559⟩, ⟨116658281910, 125364710120⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 199229440 200540160 309657600 315228160 ⟨⟨123996240260, 123996240263⟩, ⟨119634231260, 128421195856⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 200540160 201850880 309657600 315228160 ⟨⟨123017449366, 123017449374⟩, ⟨118679359177, 127418022661⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 201850880 203161600 304087040 309657600 ⟨⟨120020727332, 120020727340⟩, ⟨115722432689, 124381077977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 203161600 204472320 304087040 309657600 ⟨⟨119066536311, 119066536317⟩, ⟨114791686510, 123402984447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 201850880 203161600 309657600 315228160 ⟨⟨122044079472, 122044079480⟩, ⟨117729690897, 126420492883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 203161600 204472320 309657600 315228160 ⟨⟨121076055271, 121076055277⟩, ⟨116785154242, 125428528008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 199229440 200540160 315228160 320798720 ⟨⟨126042755108, 126042755112⟩, ⟨121664624439, 130483790252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 200540160 201850880 315228160 320798720 ⟨⟨125050170859, 125050170865⟩, ⟨120695997815, 129466789678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 199229440 200540160 320798720 326369280 ⟨⟨128084737343, 128084737345⟩, ⟨123690538625, 132541796893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 200540160 201850880 320798720 326369280 ⟨⟨127078453161, 127078453169⟩, ⟨122708249240, 131511064025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 201850880 203161600 315228160 320798720 ⟨⟨124063033558, 124063033564⟩, ⟨119732602099, 128455457196⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 203161600 204472320 315228160 320798720 ⟨⟨123081267897, 123081267905⟩, ⟨118774365075, 127449714327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 201850880 203161600 320798720 326369280 ⟨⟨126077640344, 126077640353⟩, ⟨121731216363, 130486022363⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 203161600 204472320 320798720 326369280 ⟨⟨125082223602, 125082223610⟩, ⟨120759367754, 129466593485⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 204472320 304087040 326369280 t = true :=
  ⟨_, (join_sr (m := 315228160) (by decide) (join_su (m := 201850880) (by decide) (join_sr (m := 309657600) (by decide) (join_su (m := 200540160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 200540160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 309657600) (by decide) (join_su (m := 203161600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 203161600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 201850880) (by decide) (join_sr (m := 320798720) (by decide) (join_su (m := 200540160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 200540160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 320798720) (by decide) (join_su (m := 203161600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 203161600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (29/80 : ℝ) (249/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  have e3 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

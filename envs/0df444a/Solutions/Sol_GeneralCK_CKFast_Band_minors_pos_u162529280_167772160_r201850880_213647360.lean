-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_167772160_r201850880_213647360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:54:17.087789+00:00
-- url     : https://prove2.me/submissions/6d5d5db4-75ab-4b40-a376-bb8889321f5c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 1/5]`, `ρ ∈ [77/320, 163/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 162529280 163840000 201850880 204800000 ⟨⟨104341834372, 104341834380⟩, ⟨100373398258, 108366440096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 162529280 163840000 204800000 207749120 ⟨⟨105731064995, 105731065004⟩, ⟨101753334572, 109764920222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 163840000 165150720 201850880 204800000 ⟨⟨103492209426, 103492209433⟩, ⟨99547115065, 107492954785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163840000 165150720 204800000 207749120 ⟨⟨104871892043, 104871892051⟩, ⟨100917527430, 108881866062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 162529280 163840000 207749120 210698240 ⟨⟨107117367992, 107117368000⟩, ⟨103130378588, 111160436833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 162529280 163840000 210698240 213647360 ⟨⟨108500765528, 108500765535⟩, ⟨104504552138, 112553012432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 163840000 165150720 207749120 210698240 ⟨⟨106248707357, 106248707363⟩, ⟨102285106874, 110267875094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 163840000 165150720 210698240 213647360 ⟨⟨107622676899, 107622676906⟩, ⟨103649874608, 111651003745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 165150720 166461440 201850880 204800000 ⟨⟨102649770645, 102649770652⟩, ⟨98727722498, 106626959570⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 165150720 166461440 204800000 207749120 ⟨⟨104019948913, 104019948919⟩, ⟨100088655279, 108006344844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 166461440 167772160 201850880 204800000 ⟨⟨101814394419, 101814394423⟩, ⟨97915102567, 105768325026⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 166461440 167772160 204800000 207749120 ⟨⟨103175111667, 103175111670⟩, ⟨99266599771, 107138226863⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 165150720 166461440 207749120 210698240 ⟨⟨105387319061, 105387319069⟩, ⟨101446813397, 109382887997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 165150720 166461440 210698240 213647360 ⟨⟨106751902014, 106751902021⟩, ⟨102802217463, 110756610261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 166461440 167772160 207749120 210698240 ⟨⟨104533078868, 104533078872⟩, ⟨100615379473, 108505345563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 166461440 167772160 210698240 213647360 ⟨⟨105888316352, 105888316354⟩, ⟨101961461703, 109869701756⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 167772160 201850880 213647360 t = true :=
  ⟨_, (join_su (m := 165150720) (by decide) (join_sr (m := 207749120) (by decide) (join_su (m := 163840000) (by decide) (join_sr (m := 204800000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 204800000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 163840000) (by decide) (join_sr (m := 210698240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 210698240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 207749120) (by decide) (join_su (m := 166461440) (by decide) (join_sr (m := 204800000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 204800000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 166461440) (by decide) (join_sr (m := 210698240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 210698240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (77/320 : ℝ) (163/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e3 : (((213647360 : ℤ) : ℝ) / (D : ℝ)) = (163/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

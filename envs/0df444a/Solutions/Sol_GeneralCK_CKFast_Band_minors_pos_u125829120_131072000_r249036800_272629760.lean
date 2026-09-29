-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_131072000_r249036800_272629760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:43:05.951058+00:00
-- url     : https://prove2.me/submissions/97047a2f-068a-4567-8533-9cd9ac15f6ad

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 5/32]`, `ρ ∈ [19/64, 13/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 125829120 127139840 249036800 254935040 ⟨⟨158667532785, 158667532795⟩, ⟨152520157998, 164927522161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 127139840 128450560 249036800 254935040 ⟨⟨157385208276, 157385208280⟩, ⟨151284397771, 163597385696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 125829120 127139840 254935040 260833280 ⟨⟨161854975347, 161854975355⟩, ⟨155689608822, 168132213399⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 127139840 128450560 254935040 260833280 ⟨⟨160554051671, 160554051677⟩, ⟨154435132940, 166783619643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 128450560 129761280 249036800 254935040 ⟨⟨156115653674, 156115653682⟩, ⟨150060756039, 162280691905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 129761280 131072000 249036800 254935040 ⟨⟨154858626302, 154858626310⟩, ⟨148849004013, 160977183720⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 128450560 129761280 254935040 260833280 ⟨⟨159265939318, 159265939328⟩, ⟨153192824579, 165448501599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 129761280 131072000 254935040 260833280 ⟨⟨157990396711, 157990396719⟩, ⟨151962455765, 164126603612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 125829120 127139840 260833280 266731520 ⟨⟨165024862264, 165024862272⟩, ⟨158841788191, 171319066228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 127139840 128450560 260833280 266731520 ⟨⟨163705663882, 163705663885⟩, ⟨157568915884, 169952344598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 125829120 127139840 266731520 272629760 ⟨⟨168177517829, 168177517839⟩, ⟨161977012518, 174488412874⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 127139840 128450560 266731520 272629760 ⟨⟨166840360574, 166840360580⟩, ⟨160686054641, 173103883915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 128450560 129761280 260833280 266731520 ⟨⟨162399312826, 162399312835⟩, ⟨156308254746, 168599126293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 129761280 131072000 260833280 266731520 ⟨⟨161105568701, 161105568708⟩, ⟨155059577700, 167259157147⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 128450560 129761280 266731520 272629760 ⟨⟨165516081470, 165516081479⟩, ⟨159407346426, 171732880703⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 129761280 131072000 266731520 272629760 ⟨⟨164204441376, 164204441386⟩, ⟨158140661773, 170375150635⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 131072000 249036800 272629760 t = true :=
  ⟨_, (join_sr (m := 260833280) (by decide) (join_su (m := 128450560) (by decide) (join_sr (m := 254935040) (by decide) (join_su (m := 127139840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 127139840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 254935040) (by decide) (join_su (m := 129761280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 129761280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 128450560) (by decide) (join_sr (m := 266731520) (by decide) (join_su (m := 127139840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 127139840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 266731520) (by decide) (join_su (m := 129761280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 129761280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (5/32 : ℝ) →
    rho ∈ Set.Icc (19/64 : ℝ) (13/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e2 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e3 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

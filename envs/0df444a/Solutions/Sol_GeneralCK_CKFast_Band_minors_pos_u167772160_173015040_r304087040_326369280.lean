-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_173015040_r304087040_326369280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:46:48.20085+00:00
-- url     : https://prove2.me/submissions/a4ad22f5-d4d0-43fa-b391-673c1d6e4ef2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 33/160]`, `ρ ∈ [29/80, 249/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 169082880 304087040 309657600 ⟨⟨146941336669, 146941336677⟩, ⟨141947486123, 152011261825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 169082880 170393600 304087040 309657600 ⟨⟨145820630177, 145820630185⟩, ⟨140857032303, 150859676620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 167772160 169082880 309657600 315228160 ⟨⟨149333912626, 149333912635⟩, ⟨144323373185, 154420325870⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 169082880 170393600 309657600 315228160 ⟨⟨148198675360, 148198675369⟩, ⟨143218387181, 153254220122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 170393600 171704320 304087040 309657600 ⟨⟨144707581305, 144707581312⟩, ⟨139773919342, 149716073695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 171704320 173015040 304087040 309657600 ⟨⟨143602074473, 143602074480⟩, ⟨138698036815, 148580332186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 170393600 171704320 309657600 315228160 ⟨⟨147071120641, 147071120648⟩, ⟨142120769432, 152096118885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 171704320 173015040 309657600 315228160 ⟨⟨145951133163, 145951133171⟩, ⟨141030409720, 150945901651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 167772160 169082880 315228160 320798720 ⟨⟨151719093657, 151719093664⟩, ⟨146691968769, 156821889931⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 169082880 170393600 315228160 320798720 ⟨⟨150569465430, 150569465437⟩, ⟨145572588000, 155641405831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 167772160 169082880 320798720 326369280 ⟨⟨154096979932, 154096979941⟩, ⟨149053371267, 159216055980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 169082880 170393600 320798720 326369280 ⟨⟨152933098023, 152933098032⟩, ⟨147919730679, 158021333123⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 170393600 171704320 315228160 320798720 ⟨⟨149427542492, 149427542501⟩, ⟨144460600736, 154468946261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 171704320 173015040 315228160 320798720 ⟨⟨148293209849, 148293209858⟩, ⟨143355896979, 153304391104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 170393600 171704320 320798720 326369280 ⟨⟨151776942029, 151776942038⟩, ⟨146793506752, 156834652670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 171704320 173015040 320798720 326369280 ⟨⟨150628397283, 150628397292⟩, ⟨145674589743, 155655894917⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 173015040 304087040 326369280 t = true :=
  ⟨_, (join_sr (m := 315228160) (by decide) (join_su (m := 170393600) (by decide) (join_sr (m := 309657600) (by decide) (join_su (m := 169082880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 169082880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 309657600) (by decide) (join_su (m := 171704320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 171704320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 170393600) (by decide) (join_sr (m := 320798720) (by decide) (join_su (m := 169082880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 169082880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 320798720) (by decide) (join_su (m := 171704320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 171704320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (33/160 : ℝ) →
    rho ∈ Set.Icc (29/80 : ℝ) (249/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e2 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  have e3 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

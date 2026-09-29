-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u166461440_167772160_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:20:09.338725+00:00
-- url     : https://prove2.me/submissions/53fc5744-14d8-4563-a519-811df897d86b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [127/640, 1/5]`, `ρ ∈ [137/1280, 73/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 166461440 166789120 89784320 91258880 ⟨⟨47636450262, 47636450268⟩, ⟨46534531113, 48743839584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 166789120 167116800 89784320 91258880 ⟨⟨47530950601, 47530950607⟩, ⟨46430879529, 48636475309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 166461440 166789120 91258880 92733440 ⟨⟨48380755921, 48380755927⟩, ⟨47277307238, 49489672447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 166789120 167116800 91258880 92733440 ⟨⟨48273730223, 48273730228⟩, ⟨47172132349, 49380779442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 167116800 167444480 89784320 91258880 ⟨⟨47425718686, 47425718692⟩, ⟨46327489484, 48529385066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 167444480 167772160 89784320 91258880 ⟨⟨47320753196, 47320753202⟩, ⟨46224359691, 48422567499⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 167116800 167444480 91258880 92733440 ⟨⟨48166975443, 48166975449⟩, ⟨47067222167, 49272163647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 167444480 167772160 91258880 92733440 ⟨⟨48060490248, 48060490254⟩, ⟨46962575392, 49163823692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 166461440 166789120 92733440 94208000 ⟨⟨49124130117, 49124130125⟩, ⟨48019155928, 50234569808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 166789120 167116800 92733440 94208000 ⟨⟨49015583839, 49015583846⟩, ⟨47912463159, 50124153565⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 166461440 166789120 94208000 95682560 ⟨⟨49866576511, 49866576517⟩, ⟨48760080821, 50978535344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 166789120 167116800 94208000 95682560 ⟨⟨49756515080, 49756515087⟩, ⟨48651875568, 50866601320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 167116800 167444480 92733440 94208000 ⟨⟨48907311622, 48907311628⟩, ⟨47806038235, 50014017673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 167444480 167772160 92733440 94208000 ⟨⟨48799312117, 48799312124⟩, ⟨47699879843, 49904160756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 167116800 167444480 94208000 95682560 ⟨⟨49646730820, 49646730826⟩, ⟨48543941265, 50754950762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 167444480 167772160 94208000 95682560 ⟨⟨49537222369, 49537222377⟩, ⟨48436276589, 50643582277⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 166461440 167772160 89784320 95682560 t = true :=
  ⟨_, (join_sr (m := 92733440) (by decide) (join_su (m := 167116800) (by decide) (join_sr (m := 91258880) (by decide) (join_su (m := 166789120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 166789120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 91258880) (by decide) (join_su (m := 167444480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 167444480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 167116800) (by decide) (join_sr (m := 94208000) (by decide) (join_su (m := 166789120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 166789120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 94208000) (by decide) (join_su (m := 167444480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 167444480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (127/640 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

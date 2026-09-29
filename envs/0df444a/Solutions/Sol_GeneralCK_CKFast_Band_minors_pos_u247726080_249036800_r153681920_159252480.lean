-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u247726080_249036800_r153681920_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:27:35.338401+00:00
-- url     : https://prove2.me/submissions/6a410da2-da4d-41e7-9d23-b301bdc3f229

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [189/640, 19/64]`, `ρ ∈ [469/2560, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 247726080 248053760 153681920 155074560 ⟨⟨46075483554, 46075483559⟩, ⟨45270991875, 46882880486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 248053760 248381440 153681920 155074560 ⟨⟨45967041684, 45967041687⟩, ⟨45163529146, 46773453861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247726080 248053760 155074560 156467200 ⟨⟨46481286781, 46481286787⟩, ⟨45675885992, 47289594296⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 248053760 248381440 155074560 156467200 ⟨⟨46371933416, 46371933419⟩, ⟨45567513158, 47179254789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 248381440 248709120 153681920 155074560 ⟨⟨45858739186, 45858739192⟩, ⟨45056203682, 46664168740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 248709120 249036800 153681920 155074560 ⟨⟨45750575547, 45750575553⟩, ⟨44949014977, 46555024589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 248381440 248709120 155074560 156467200 ⟨⟨46262720307, 46262720314⟩, ⟨45459278473, 47069057670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 248709120 249036800 155074560 156467200 ⟨⟨46153646940, 46153646945⟩, ⟨45351181429, 46959002408⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 247726080 248053760 156467200 157859840 ⟨⟨46886928515, 46886928520⟩, ⟨46080618836, 47696146389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 248053760 248381440 156467200 157859840 ⟨⟨46776664726, 46776664729⟩, ⟨45971336965, 47584895074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 247726080 248053760 157859840 159252480 ⟨⟨47292409118, 47292409125⟩, ⟨46485190768, 48102537128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 248053760 248381440 157859840 159252480 ⟨⟨47181235974, 47181235977⟩, ⟨46375000926, 47990375080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 248381440 248709120 156467200 157859840 ⟨⟨46666542073, 46666542078⟩, ⟨45862194121, 47473787030⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 248709120 249036800 156467200 157859840 ⟨⟨46556560036, 46556560042⟩, ⟨45753189794, 47362821719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 248381440 248709120 157859840 159252480 ⟨⟨47070204839, 47070204844⟩, ⟨46264950982, 47878357176⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 248709120 249036800 157859840 159252480 ⟨⟨46959315192, 46959315197⟩, ⟨46155040424, 47766482879⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 247726080 249036800 153681920 159252480 t = true :=
  ⟨_, (join_sr (m := 156467200) (by decide) (join_su (m := 248381440) (by decide) (join_sr (m := 155074560) (by decide) (join_su (m := 248053760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 248053760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 155074560) (by decide) (join_su (m := 248709120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 248709120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 248381440) (by decide) (join_sr (m := 157859840) (by decide) (join_su (m := 248053760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 248053760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 157859840) (by decide) (join_su (m := 248709120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 248709120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (189/640 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (469/2560 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((247726080 : ℤ) : ℝ) / (D : ℝ)) = (189/640 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u141557760_146800640_r249036800_272629760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:43:28.174698+00:00
-- url     : https://prove2.me/submissions/cd3ec16d-a30b-4a60-be78-769fc02e7d90

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [27/160, 7/40]`, `ρ ∈ [19/64, 13/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 141557760 142868480 249036800 254935040 ⟨⟨144071950478, 144071950487⟩, ⟨138443228532, 149799622812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 142868480 144179200 249036800 254935040 ⟨⟨142928105534, 142928105543⟩, ⟨137338968668, 148615171847⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 141557760 142868480 254935040 260833280 ⟨⟨147039144346, 147039144353⟩, ⟨141391477364, 152785278023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 142868480 144179200 254935040 260833280 ⟨⟨145877255144, 145877255154⟩, ⟨140269131448, 151582842310⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 144179200 145489920 249036800 254935040 ⟨⟨141794483149, 141794483157⟩, ⟨136244423705, 147441467400⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 145489920 146800640 249036800 254935040 ⟨⟨140670902677, 140670902684⟩, ⟨135159422998, 146278318474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 144179200 145489920 254935040 260833280 ⟨⟨144725638942, 144725638951⟩, ⟨139156555697, 150391198216⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 145489920 146800640 254935040 260833280 ⟨⟨143584115508, 143584115515⟩, ⟨138053579700, 149210155359⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 141557760 142868480 260833280 266731520 ⟨⟨149992336749, 149992336756⟩, ⟨144325948857, 155756706761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 142868480 144179200 260833280 266731520 ⟨⟨148812668098, 148812668106⟩, ⟨143185777007, 154536555674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 141557760 142868480 266731520 272629760 ⟨⟨152931762394, 152931762404⟩, ⟨147246872410, 158714149090⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 142868480 144179200 266731520 272629760 ⟨⟨151734572860, 151734572867⟩, ⟨146089128676, 157476545589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 144179200 145489920 260833280 266731520 ⟨⟨147643318410, 147643318418⟩, ⟨142055426161, 153327236791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 145489920 146800640 260833280 266731520 ⟨⟨146484107941, 146484107949⟩, ⟨140934726223, 152128560406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 144179200 145489920 266731520 272629760 ⟨⟨150547743941, 150547743949⟩, ⟨144941252531, 156249810524⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 145489920 146800640 266731520 272629760 ⟨⟨149371096450, 149371096459⟩, ⟨143803074252, 155033754934⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 141557760 146800640 249036800 272629760 t = true :=
  ⟨_, (join_sr (m := 260833280) (by decide) (join_su (m := 144179200) (by decide) (join_sr (m := 254935040) (by decide) (join_su (m := 142868480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 142868480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 254935040) (by decide) (join_su (m := 145489920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 145489920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 144179200) (by decide) (join_sr (m := 266731520) (by decide) (join_su (m := 142868480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 142868480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 266731520) (by decide) (join_su (m := 145489920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 145489920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (27/160 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (19/64 : ℝ) (13/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e3 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

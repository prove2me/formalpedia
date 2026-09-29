-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_209715200_r660602880_682885120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:03:28.321435+00:00
-- url     : https://prove2.me/submissions/4f49aab7-98e5-4b87-af78-a8f2f545cb01

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 1/4]`, `ρ ∈ [63/80, 521/640]` by 12 cells of the computing
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
theorem cell0 : cellOK 199229440 201850880 660602880 671744000 ⟨⟨245971949872, 245971949881⟩, ⟨235444459353, 256728628713⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 201850880 204472320 660602880 671744000 ⟨⟨242550908097, 242550908101⟩, ⟨232118703396, 253211190270⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 199229440 201850880 671744000 682885120 ⟨⟨249652269247, 249652269257⟩, ⟨239068996689, 260463668134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 201850880 204472320 671744000 682885120 ⟨⟨246191287983, 246191287988⟩, ⟨235703129194, 256906546985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 204472320 207093760 660602880 666173440 ⟨⟨238248482427, 238248482437⟩, ⟨229340964557, 247321597908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 204472320 207093760 666173440 671744000 ⟨⟨240050427694, 240050427704⟩, ⟨231116246013, 249149987129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 207093760 209715200 660602880 666173440 ⟨⟨234876779992, 234876780001⟩, ⟨226037719017, 243880920361⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 207093760 209715200 666173440 671744000 ⟨⟨236658485186, 236658485196⟩, ⟨227792713392, 245689144105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 207093760 671744000 677314560 ⟨⟨241850539856, 241850539866⟩, ⟨232889720031, 250976512484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 204472320 207093760 677314560 682885120 ⟨⟨243648847323, 243648847332⟩, ⟨234661414483, 252801202896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 207093760 209715200 671744000 677314560 ⟨⟨238438422203, 238438422212⟩, ⟨229545963280, 247495570962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 207093760 209715200 677314560 682885120 ⟨⟨240216618291, 240216618302⟩, ⟨231297495427, 249300228674⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 209715200 660602880 682885120 t = true :=
  ⟨_, (join_su (m := 204472320) (by decide) (join_sr (m := 671744000) (by decide) (join_su (m := 201850880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 201850880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 671744000) (by decide) (join_su (m := 207093760) (by decide) (join_sr (m := 666173440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 666173440) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 207093760) (by decide) (join_sr (m := 677314560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 677314560) (by decide) (leaf_ok cell10) (leaf_ok cell11)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (63/80 : ℝ) (521/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((660602880 : ℤ) : ℝ) / (D : ℝ)) = (63/80 : ℝ) := by norm_num [D]
  have e3 : (((682885120 : ℤ) : ℝ) / (D : ℝ)) = (521/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

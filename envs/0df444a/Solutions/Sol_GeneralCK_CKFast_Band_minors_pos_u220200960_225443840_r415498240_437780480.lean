-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_225443840_r415498240_437780480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:28:48.100758+00:00
-- url     : https://prove2.me/submissions/572ad5a4-b260-41cd-99e5-6621c9eeb0c9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 43/160]`, `ρ ∈ [317/640, 167/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 221511680 415498240 421068800 ⟨⟨143178703598, 143178703605⟩, ⟨138887602364, 147526124272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 221511680 222822400 415498240 421068800 ⟨⟨142035300498, 142035300506⟩, ⟨137765806530, 146360789043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 220200960 221511680 421068800 426639360 ⟨⟨144952226552, 144952226561⟩, ⟨140646261897, 149314509253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 221511680 222822400 421068800 426639360 ⟨⟨143796644292, 143796644300⟩, ⟨139512319504, 148136965809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 222822400 224133120 415498240 421068800 ⟨⟨140896534402, 140896534408⟩, ⟨136648490535, 145200250563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 224133120 225443840 415498240 421068800 ⟨⟨139762347358, 139762347364⟩, ⟨135535598290, 144044448998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222822400 224133120 421068800 426639360 ⟨⟨142645704334, 142645704342⟩, ⟨138382863285, 146964223298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 224133120 225443840 421068800 426639360 ⟨⟨141499348875, 141499348884⟩, ⟨137257837274, 145796222059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 220200960 221511680 426639360 432209920 ⟨⟨146723145485, 146723145493⟩, ⟨142402341227, 151100265180⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 221511680 222822400 426639360 432209920 ⟨⟨145555439244, 145555439251⟩, ⟨141256306496, 149910569671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 220200960 221511680 432209920 437780480 ⟨⟨148491489889, 148491489896⟩, ⟨144155869518, 152883421868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 221511680 222822400 432209920 437780480 ⟨⟨147311714092, 147311714100⟩, ⟨142997795939, 151681629679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 222822400 224133120 426639360 432209920 ⟨⟨144392379743, 144392379749⟩, ⟨140114763433, 148725678403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 224133120 225443840 426639360 432209920 ⟨⟨143233909340, 143233909348⟩, ⟨138977656204, 147545531901⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 222822400 224133120 432209920 437780480 ⟨⟨146136588634, 146136588642⟩, ⟨141844218691, 150484644183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 224133120 225443840 432209920 437780480 ⟨⟨144966056040, 144966056047⟩, ⟨140695082084, 149292406100⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 225443840 415498240 437780480 t = true :=
  ⟨_, (join_sr (m := 426639360) (by decide) (join_su (m := 222822400) (by decide) (join_sr (m := 421068800) (by decide) (join_su (m := 221511680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 221511680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 421068800) (by decide) (join_su (m := 224133120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 224133120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 222822400) (by decide) (join_sr (m := 432209920) (by decide) (join_su (m := 221511680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 221511680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 432209920) (by decide) (join_su (m := 224133120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 224133120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (317/640 : ℝ) (167/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  have e3 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

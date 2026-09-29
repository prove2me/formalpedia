-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u183500800_188743680_r304087040_326369280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:46:48.115802+00:00
-- url     : https://prove2.me/submissions/018fc00e-e8b4-43b1-87e2-b56e5a79ce7b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/32, 9/40]`, `ρ ∈ [29/80, 249/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 183500800 184811520 304087040 309657600 ⟨⟨133973878583, 133973878591⟩, ⟨129323235959, 138693576789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 184811520 186122240 304087040 309657600 ⟨⟨132937892198, 132937892207⟩, ⟨128314018581, 137630281948⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 183500800 184811520 309657600 315228160 ⟨⟨136193782268, 136193782277⟩, ⟨131526580953, 140929930646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 184811520 186122240 309657600 315228160 ⟨⟨135143578596, 135143578604⟩, ⟨130503169878, 139852401413⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 186122240 187432960 304087040 309657600 ⟨⟨131908310016, 131908310020⟩, ⟨127310943851, 136573659329⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 187432960 188743680 304087040 309657600 ⟨⟨130885039495, 130885039503⟩, ⟨126313923248, 135523612277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 186122240 187432960 309657600 315228160 ⟨⟨134099806254, 134099806258⟩, ⟨129485930257, 138781569692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 187432960 188743680 309657600 315228160 ⟨⟨133062372792, 133062372801⟩, ⟨128474773604, 137717338974⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 183500800 184811520 315228160 320798720 ⟨⟨138407830995, 138407831003⟩, ⟨133724147720, 143160351147⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 184811520 186122240 315228160 320798720 ⟨⟨137343525510, 137343525519⟩, ⟨132686656395, 142068705034⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 183500800 184811520 320798720 326369280 ⟨⟨140616098241, 140616098249⟩, ⟨135916008568, 145384912954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 184811520 186122240 320798720 326369280 ⟨⟨139537804529, 139537804537⟩, ⟨134864548592, 144279265537⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 186122240 187432960 315228160 320798720 ⟨⟨136285676633, 136285676637⟩, ⟨131655363508, 140983779839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 187432960 188743680 315228160 320798720 ⟨⟨135234192025, 135234192032⟩, ⟨130630180630, 139905479227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 186122240 187432960 320798720 326369280 ⟨⟨138465990891, 138465990893⟩, ⟨133819312254, 143180360607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 187432960 188743680 320798720 326369280 ⟨⟨137400565127, 137400565136⟩, ⟨132780211216, 142088102028⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 183500800 188743680 304087040 326369280 t = true :=
  ⟨_, (join_sr (m := 315228160) (by decide) (join_su (m := 186122240) (by decide) (join_sr (m := 309657600) (by decide) (join_su (m := 184811520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 184811520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 309657600) (by decide) (join_su (m := 187432960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 187432960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 186122240) (by decide) (join_sr (m := 320798720) (by decide) (join_su (m := 184811520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 184811520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 320798720) (by decide) (join_su (m := 187432960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 187432960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/32 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (29/80 : ℝ) (249/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  have e3 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

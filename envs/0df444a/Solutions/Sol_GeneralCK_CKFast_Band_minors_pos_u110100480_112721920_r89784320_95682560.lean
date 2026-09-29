-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u110100480_112721920_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:04:56.082249+00:00
-- url     : https://prove2.me/submissions/0f8b57fa-0600-4421-8545-0a3f57640648

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/160, 43/320]`, `ρ ∈ [137/1280, 73/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 110100480 110755840 89784320 91258880 ⟨⟨71267380295, 71267380302⟩, ⟨68849476871, 73710042799⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 110100480 110755840 91258880 92733440 ⟨⟨72334690244, 72334690251⟩, ⟨69913286377, 74780814845⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 110755840 111411200 89784320 91258880 ⟨⟨70903632287, 70903632294⟩, ⟨68496528127, 73335292852⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 110755840 111411200 91258880 92733440 ⟨⟨71966268199, 71966268208⟩, ⟨69555671971, 74401383405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 110100480 110755840 92733440 94208000 ⟨⟨73399398111, 73399398118⟩, ⟨70974516552, 75848962004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 110100480 110755840 94208000 95682560 ⟨⟨74461520171, 74461520179⟩, ⟨72033183454, 76914500770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 110755840 111411200 92733440 94208000 ⟨⟨73026334341, 73026334348⟩, ⟨70612268441, 75464881732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 110755840 111411200 94208000 95682560 ⟨⟨74083846683, 74083846690⟩, ⟨71666333306, 76525804015⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 111411200 112066560 89784320 91258880 ⟨⟨70542758817, 70542758825⟩, ⟨68146344270, 72963529865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 111411200 112066560 91258880 92733440 ⟨⟨71600748060, 71600748070⟩, ⟨69200849917, 74024966172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 112066560 112721920 89784320 91258880 ⟨⟨70184720661, 70184720669⟩, ⟨67798887760, 72594712873⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 112066560 112721920 91258880 92733440 ⟨⟨71238090335, 71238090344⟩, ⟨68848782409, 73651521916⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 111411200 112066560 92733440 94208000 ⟨⟨72656199389, 72656199399⟩, ⟨70252839708, 75083842450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 111411200 112066560 94208000 95682560 ⟨⟨73709128484, 73709128494⟩, ⟨71302329113, 76140174592⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 112066560 112721920 92733440 94208000 ⟨⟨72288953512, 72288953519⟩, ⟨69896192277, 74705802687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 112066560 112721920 94208000 95682560 ⟨⟨73337325580, 73337325588⟩, ⟨70941132553, 75757570776⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 110100480 112721920 89784320 95682560 t = true :=
  ⟨_, (join_su (m := 111411200) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 110755840) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 91258880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 110755840) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 94208000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 92733440) (by decide) (join_su (m := 112066560) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 91258880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 112066560) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 94208000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/160 : ℝ) (43/320 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e1 : (((112721920 : ℤ) : ℝ) / (D : ℝ)) = (43/320 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

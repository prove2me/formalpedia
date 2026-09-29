-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_120586240_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:27:39.980573+00:00
-- url     : https://prove2.me/submissions/a42cbf73-a654-4a5f-b462-a805edeb006b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 23/160]`, `ρ ∈ [5/32, 109/640]` by 18 cells of the computing
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
theorem cell0 : cellOK 115343360 116654080 131072000 134021120 ⟨⟨96703210906, 96703210916⟩, ⟨91885488930, 101609781825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 115343360 116654080 134021120 136970240 ⟨⟨98634822058, 98634822068⟩, ⟨93805384576, 103552848434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 116654080 117964800 131072000 134021120 ⟨⟨95792555436, 95792555445⟩, ⟨91014616896, 100658075075⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 116654080 117964800 134021120 136970240 ⟨⟨97709355794, 97709355802⟩, ⟨92919718788, 102586325387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 115343360 116654080 136970240 139919360 ⟨⟨100558539325, 100558539333⟩, ⟨95717509839, 105487897185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 115343360 116654080 139919360 142868480 ⟨⟨102474451040, 102474451050⟩, ⟨97621951003, 107415018493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 116654080 117964800 136970240 139919360 ⟨⟨99618439415, 99618439423⟩, ⟨94817224165, 104506738229⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 116654080 117964800 139919360 142868480 ⟨⟨101519891709, 101519891719⟩, ⟨96707216469, 106419401008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 117964800 118620160 131072000 134021120 ⟨⟨95117733986, 95117733995⟩, ⟨92089828336, 98180691339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 118620160 119275520 131072000 134021120 ⟨⟨94671672896, 94671672903⟩, ⟨91657119554, 97721013225⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 117964800 119275520 134021120 136970240 ⟨⟨96796438906, 96796438916⟩, ⟨92045878974, 101633104924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 119275520 119930880 131072000 134021120 ⟨⟨94228624714, 94228624719⟩, ⟨91227305159, 97264469696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 119930880 120586240 131072000 134021120 ⟨⟨93788553260, 93788553268⟩, ⟨90800350587, 96811022908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 119275520 120586240 134021120 136970240 ⟨⟨95895770776, 95895770786⟩, ⟨91183584225, 100692865762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 117964800 119275520 136970240 139919360 ⟨⟨98691009460, 98691009468⟩, ⟨93928887621, 103538999406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 117964800 119275520 139919360 142868480 ⟨⟨100578118799, 100578118807⟩, ⟨95804550184, 105437317019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 119275520 120586240 136970240 139919360 ⟨⟨97775947436, 97775947443⟩, ⟨93052217739, 102584358199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 119275520 120586240 139919360 142868480 ⟨⟨99648828984, 99648828992⟩, ⟨94913668226, 104468442884⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 120586240 131072000 142868480 t = true :=
  ⟨_, (join_su (m := 117964800) (by decide) (join_sr (m := 136970240) (by decide) (join_su (m := 116654080) (by decide) (join_sr (m := 134021120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 134021120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 116654080) (by decide) (join_sr (m := 139919360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 139919360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 136970240) (by decide) (join_su (m := 119275520) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 118620160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 134021120) (by decide) (join_su (m := 119930880) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))) (join_su (m := 119275520) (by decide) (join_sr (m := 139919360) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_sr (m := 139919360) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (23/160 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

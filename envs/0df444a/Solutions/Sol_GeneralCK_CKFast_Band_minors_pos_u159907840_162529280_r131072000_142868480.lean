-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u159907840_162529280_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:40:20.383176+00:00
-- url     : https://prove2.me/submissions/da511b0d-3586-40b5-a316-85c1ed65de3d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [61/320, 31/160]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 159907840 160563200 131072000 134021120 ⟨⟨71433690086, 71433690092⟩, ⟨69074136131, 73816096580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 160563200 161218560 131072000 134021120 ⟨⟨71125969405, 71125969413⟩, ⟨68774538714, 73500118242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 159907840 160563200 134021120 136970240 ⟨⟨72925878639, 72925878646⟩, ⟨70560488001, 75314093188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 160563200 161218560 134021120 136970240 ⟨⟨72612455840, 72612455848⟩, ⟨70255203493, 74992398474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 161218560 161873920 131072000 134021120 ⟨⟨70819762568, 70819762576⟩, ⟨68476400438, 73185709702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 161873920 162529280 131072000 134021120 ⟨⟨70515055079, 70515055082⟩, ⟨68179707385, 72872855870⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 161218560 161873920 134021120 136970240 ⟨⟨72300566914, 72300566922⟩, ⟨69951398195, 74672293532⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 161873920 162529280 134021120 136970240 ⟨⟨71990197228, 71990197231⟩, ⟨69649058051, 74353763137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 159907840 160563200 136970240 139919360 ⟨⟨74414361451, 74414361457⟩, ⟨72043166003, 76808351982⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 160563200 161218560 136970240 139919360 ⟨⟨74095277741, 74095277748⟩, ⟨71732235148, 76480982560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 159907840 160563200 139919360 142868480 ⟨⟨75899168109, 75899168115⟩, ⟨73522199381, 78298902898⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 160563200 161218560 139919360 142868480 ⟨⟨75574464230, 75574464236⟩, ⟨73205662464, 77965899966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 161218560 161873920 136970240 139919360 ⟨⟨73777747485, 73777747492⟩, ⟨71422803130, 76155222433⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 161873920 162529280 136970240 139919360 ⟨⟨73461755920, 73461755922⟩, ⟨71114855762, 75831056246⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 161218560 161873920 139919360 142868480 ⟨⟨75251332948, 75251332955⟩, ⟨72890643583, 77634525408⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 161873920 162529280 139919360 142868480 ⟨⟨74929759375, 74929759378⟩, ⟨72577128418, 77304763744⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 159907840 162529280 131072000 142868480 t = true :=
  ⟨_, (join_sr (m := 136970240) (by decide) (join_su (m := 161218560) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 160563200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 160563200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 134021120) (by decide) (join_su (m := 161873920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 161873920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 161218560) (by decide) (join_sr (m := 139919360) (by decide) (join_su (m := 160563200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 160563200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 139919360) (by decide) (join_su (m := 161873920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 161873920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (61/320 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

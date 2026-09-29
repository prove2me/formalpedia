-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u152043520_154664960_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:39:17.848367+00:00
-- url     : https://prove2.me/submissions/ab9021e8-5e02-48c0-9dea-3a74acd92e6b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [29/160, 59/320]`, `ρ ∈ [109/640, 59/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 152043520 152698880 142868480 145817600 ⟨⟨81473584437, 81473584442⟩, ⟨78988236043, 83983345019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 152698880 153354240 142868480 145817600 ⟨⟨81122962722, 81122962730⟩, ⟨78646496511, 83623694128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 152043520 152698880 145817600 148766720 ⟨⟨83019076526, 83019076531⟩, ⟨80527864217, 85534661302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 152698880 153354240 145817600 148766720 ⟨⟨82662686024, 82662686032⟩, ⟨80180368136, 85169230332⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 153354240 154009600 142868480 145817600 ⟨⟨80774127981, 80774127989⟩, ⟨78306481942, 83265893621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 154009600 154664960 142868480 145817600 ⟨⟨80427062737, 80427062745⟩, ⟨77968175536, 82909925327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 153354240 154009600 145817600 148766720 ⟨⟨82308102227, 82308102235⟩, ⟨79834616847, 84805669360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 154009600 154664960 145817600 148766720 ⟨⟨81955307536, 81955307542⟩, ⟨79490593423, 84443960096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 152043520 152698880 148766720 151715840 ⟨⟨84560472427, 84560472431⟩, ⟨82063432366, 87081845050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 152698880 153354240 148766720 151715840 ⟨⟨84198357936, 84198357943⟩, ⟨81710224030, 86710679298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 152043520 152698880 151715840 154664960 ⟨⟨86097806448, 86097806450⟩, ⟨83594974377, 88624930993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 152698880 153354240 151715840 154664960 ⟨⟨85730012235, 85730012241⟩, ⟨83236097559, 88248075219⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 153354240 154009600 148766720 151715840 ⟨⟨83838069401, 83838069409⟩, ⟨81358779842, 86341402674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 154009600 154664960 148766720 151715840 ⟨⟨83479589103, 83479589111⟩, ⟨81009082754, 85973996773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 153354240 154009600 151715840 154664960 ⟨⟨85364062756, 85364062763⟩, ⟨82879003781, 87873127224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 154009600 154664960 151715840 154664960 ⟨⟨84999940182, 84999940189⟩, ⟨82523675877, 87500068498⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 152043520 154664960 142868480 154664960 t = true :=
  ⟨_, (join_sr (m := 148766720) (by decide) (join_su (m := 153354240) (by decide) (join_sr (m := 145817600) (by decide) (join_su (m := 152698880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 152698880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 145817600) (by decide) (join_su (m := 154009600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 154009600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 153354240) (by decide) (join_sr (m := 151715840) (by decide) (join_su (m := 152698880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 152698880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 151715840) (by decide) (join_su (m := 154009600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 154009600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (29/160 : ℝ) (59/320 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e1 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

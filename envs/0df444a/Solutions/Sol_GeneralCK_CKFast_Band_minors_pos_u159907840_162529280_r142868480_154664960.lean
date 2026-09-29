-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u159907840_162529280_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:40:27.342299+00:00
-- url     : https://prove2.me/submissions/338b64af-1c6b-41f8-9baf-db7fb0bfca85

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [61/320, 31/160]`, `ρ ∈ [109/640, 59/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 159907840 160563200 142868480 145817600 ⟨⟨77380327913, 77380327919⟩, ⟨74997617095, 79785775577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 160563200 161218560 142868480 145817600 ⟨⟨77050044152, 77050044158⟩, ⟨74675513956, 79447179871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 159907840 160563200 145817600 148766720 ⟨⟨78857869881, 78857869889⟩, ⟨76469447826, 81268999379⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 160563200 161218560 145817600 148766720 ⟨⟨78522046075, 78522046083⟩, ⟨76141817862, 80924851176⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 161218560 161873920 142868480 145817600 ⟨⟨76721351700, 76721351707⟩, ⟨74354947624, 79110231180⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 161873920 162529280 142868480 145817600 ⟨⟨76394235549, 76394235552⟩, ⟨74035903655, 78774913908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 161218560 161873920 145817600 148766720 ⟨⟨78187831867, 78187831875⟩, ⟨75815743057, 80582368201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 161873920 162529280 145817600 148766720 ⟨⟨77855212132, 77855212135⟩, ⟨75491208848, 80241534743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 159907840 160563200 148766720 151715840 ⟨⟨80331822752, 80331822759⟩, ⟨77937719981, 82748603373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 160563200 161218560 148766720 151715840 ⟨⟨79990498294, 79990498302⟩, ⟨77604602152, 82398942502⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 159907840 160563200 151715840 154664960 ⟨⟨81802214990, 81802214997⟩, ⟨79402461697, 84224616354⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 160563200 161218560 151715840 154664960 ⟨⟨81455428837, 81455428843⟩, ⟨79063894529, 83869482196⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 161218560 161873920 148766720 151715840 ⟨⟨79650801306, 79650801313⟩, ⟨77273057419, 82050964647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 161873920 162529280 148766720 151715840 ⟨⟨79312716550, 79312716553⟩, ⟨76943071112, 81704653991⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 161218560 161873920 151715840 154664960 ⟨⟨81110287612, 81110287618⟩, ⟨78726917995, 83516048429⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 161873920 162529280 151715840 154664960 ⟨⟨80766775975, 80766775977⟩, ⟨78391517310, 83164299132⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 159907840 162529280 142868480 154664960 t = true :=
  ⟨_, (join_sr (m := 148766720) (by decide) (join_su (m := 161218560) (by decide) (join_sr (m := 145817600) (by decide) (join_su (m := 160563200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 160563200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 145817600) (by decide) (join_su (m := 161873920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 161873920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 161218560) (by decide) (join_sr (m := 151715840) (by decide) (join_su (m := 160563200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 160563200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 151715840) (by decide) (join_su (m := 161873920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 161873920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (61/320 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

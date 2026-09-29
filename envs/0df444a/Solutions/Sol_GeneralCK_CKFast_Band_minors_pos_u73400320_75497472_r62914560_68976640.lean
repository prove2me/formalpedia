-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u73400320_75497472_r62914560_68976640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:28:54.554797+00:00
-- url     : https://prove2.me/submissions/74bdd880-e285-46c6-bed0-7b9704d49ac8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/80, 9/100]`, `ρ ∈ [3/40, 421/5120]` by 16 cells of the computing
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
theorem cell0 : cellOK 73400320 73924608 62914560 64430080 ⟨⟨71752976523, 71752976535⟩, ⟨68966263126, 74574372800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 73400320 73924608 64430080 65945600 ⟨⟨73286512260, 73286512272⟩, ⟨70495780829, 76111798135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 73924608 74448896 62914560 64430080 ⟨⟨71364949576, 71364949585⟩, ⟨68593452985, 74170773870⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 73924608 74448896 64430080 65945600 ⟨⟨72891621751, 72891621760⟩, ⟨70116108855, 75701336682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 73400320 73924608 65945600 67461120 ⟨⟨74813165536, 74813165548⟩, ⟨72018484757, 77642272625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 73400320 73924608 67461120 68976640 ⟨⟨76333006234, 76333006246⟩, ⟨73534443596, 79165867363⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 73924608 74448896 65945600 67461120 ⟨⟨74411496841, 74411496850⟩, ⟨71632035292, 77225035047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 73924608 74448896 67461120 68976640 ⟨⟨75924643397, 75924643407⟩, ⟨73141299679, 78741938692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 74448896 74973184 62914560 64430080 ⟨⟨70980769337, 70980769346⟩, ⟨68224305598, 73771211445⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 74448896 74973184 64430080 65945600 ⟨⟨72500628052, 72500628064⟩, ⟨69740150184, 75294961327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 74973184 75497472 62914560 64430080 ⟨⟨70600373460, 70600373472⟩, ⟨67858761992, 73375619683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 74973184 75497472 64430080 65945600 ⟨⟨72113468270, 72113468279⟩, ⟨69367845271, 74892605689⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 74448896 74973184 65945600 67461120 ⟨⟨74013773740, 74013773752⟩, ⟨71249348376, 76811931817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 74448896 74973184 67461120 68976640 ⟨⟨75520273648, 75520273660⟩, ⟨72751966282, 78322191320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 74973184 75497472 65945600 67461120 ⟨⟨73619932811, 73619932822⟩, ⟨70870363918, 76402896056⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 74973184 75497472 67461120 68976640 ⟨⟨75119833067, 75119833076⟩, ⟨72366382796, 77906557880⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 73400320 75497472 62914560 68976640 t = true :=
  ⟨_, (join_su (m := 74448896) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 73924608) (by decide) (join_sr (m := 64430080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 64430080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 73924608) (by decide) (join_sr (m := 67461120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 67461120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 65945600) (by decide) (join_su (m := 74973184) (by decide) (join_sr (m := 64430080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 64430080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 74973184) (by decide) (join_sr (m := 67461120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 67461120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/80 : ℝ) (9/100 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (421/5120 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((73400320 : ℤ) : ℝ) / (D : ℝ)) = (7/80 : ℝ) := by norm_num [D]
  have e1 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((68976640 : ℤ) : ℝ) / (D : ℝ)) = (421/5120 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

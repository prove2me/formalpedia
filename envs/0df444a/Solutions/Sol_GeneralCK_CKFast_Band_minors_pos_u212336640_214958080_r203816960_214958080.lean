-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u212336640_214958080_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:37:39.493061+00:00
-- url     : https://prove2.me/submissions/c8eb3011-aa10-42d0-99cb-b6b13d80f5e1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [81/320, 41/160]`, `ρ ∈ [311/1280, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 212336640 212992000 203816960 206602240 ⟨⟨77070762646, 77070762651⟩, ⟨75149862835, 79006257677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 212992000 213647360 203816960 206602240 ⟨⟨76744640188, 76744640194⟩, ⟨74828956147, 78674858829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212336640 212992000 206602240 209387520 ⟨⟨78067623634, 78067623640⟩, ⟨76142581790, 80007264028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212992000 213647360 206602240 209387520 ⟨⟨77737664939, 77737664947⟩, ⟨75817848782, 79672019232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 213647360 214302720 203816960 206602240 ⟨⟨76419510189, 76419510195⟩, ⟨74509016642, 78344478114⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 214302720 214958080 203816960 206602240 ⟨⟨76095365232, 76095365233⟩, ⟨74190037100, 78015107916⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 213647360 214302720 206602240 209387520 ⟨⟨77408705984, 77408705992⟩, ⟨75494090251, 79337799834⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 214302720 214958080 206602240 209387520 ⟨⟨77080739317, 77080739321⟩, ⟨75171298941, 79004598184⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 212336640 212992000 209387520 212172800 ⟨⟨79063340679, 79063340684⟩, ⟨77134163063, 81007120084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 212992000 213647360 209387520 212172800 ⟨⟨78729558862, 78729558869⟩, ⟨76805616731, 80668042573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 212336640 212992000 212172800 214958080 ⟨⟨80057919976, 80057919982⟩, ⟨78124612811, 82005832084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 212992000 213647360 212172800 214958080 ⟨⟨79720328059, 79720328066⟩, ⟨77792266061, 81662934997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 213647360 214302720 209387520 212172800 ⟨⟨78396783940, 78396783947⟩, ⟨76478052045, 80329997600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 214302720 214958080 209387520 212172800 ⟨⟨78065008425, 78065008429⟩, ⟨76151461717, 79992977476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 213647360 214302720 212172800 214958080 ⟨⟨79383750068, 79383750074⟩, ⟨77460908005, 81321077462⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 214302720 214958080 212172800 214958080 ⟨⟨79048178481, 79048178486⟩, ⟨77130531317, 80980251755⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 212336640 214958080 203816960 214958080 t = true :=
  ⟨_, (join_sr (m := 209387520) (by decide) (join_su (m := 213647360) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 212992000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 212992000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 206602240) (by decide) (join_su (m := 214302720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 214302720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 213647360) (by decide) (join_sr (m := 212172800) (by decide) (join_su (m := 212992000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 212992000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 212172800) (by decide) (join_su (m := 214302720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 214302720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (81/320 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

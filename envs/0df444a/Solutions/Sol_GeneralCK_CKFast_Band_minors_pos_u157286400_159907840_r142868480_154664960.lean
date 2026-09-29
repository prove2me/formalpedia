-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_159907840_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:40:13.432362+00:00
-- url     : https://prove2.me/submissions/6a1cac9f-eda2-4235-aead-a92f44e3e18a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 61/320]`, `ρ ∈ [109/640, 59/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 157941760 142868480 145817600 ⟨⟨78717682896, 78717682902⟩, ⟨76301692868, 81156947377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157941760 158597120 142868480 145817600 ⟨⟨78380879992, 78380879999⟩, ⟨75973294462, 80811603694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157286400 157941760 145817600 148766720 ⟨⟨80217570267, 80217570275⟩, ⟨77795816809, 82662565568⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 157941760 158597120 145817600 148766720 ⟨⟨79875152994, 79875153001⟩, ⟨77461816975, 82311595396⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 158597120 159252480 142868480 145817600 ⟨⟨78045730349, 78045730352⟩, ⟨75646492452, 80467971398⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 159252480 159907840 142868480 145817600 ⟨⟨77712218181, 77712218188⟩, ⟨75321271658, 80126034089⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 158597120 159252480 145817600 148766720 ⟨⟨79534407739, 79534407742⟩, ⟨77129432365, 81962355282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 159252480 159907840 145817600 148766720 ⟨⟨79195318600, 79195318606⟩, ⟨76798647685, 81614828712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 157286400 157941760 148766720 151715840 ⟨⟨81713706701, 81713706708⟩, ⟨79286222125, 84164400319⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 157941760 158597120 148766720 151715840 ⟨⟨81365716167, 81365716176⟩, ⟨78946661514, 83807845225⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 157286400 157941760 151715840 154664960 ⟨⟨83206122484, 83206122491⟩, ⟨80772938745, 85662482278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 157941760 158597120 151715840 154664960 ⟨⟨82852599335, 82852599342⟩, ⟨80427857554, 85300383357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 158597120 159252480 148766720 151715840 ⟨⟨81019415975, 81019415979⟩, ⟨78608734530, 83453038419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 159252480 159907840 148766720 151715840 ⟨⟨80674790106, 80674790113⟩, ⟨78272425761, 83099963274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 158597120 159252480 151715840 154664960 ⟨⟨82500784419, 82500784421⟩, ⟨80084427968, 84940050514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 159252480 159907840 151715840 154664960 ⟨⟨82150661609, 82150661616⟩, ⟨79742634461, 84581467020⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 159907840 142868480 154664960 t = true :=
  ⟨_, (join_sr (m := 148766720) (by decide) (join_su (m := 158597120) (by decide) (join_sr (m := 145817600) (by decide) (join_su (m := 157941760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 157941760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 145817600) (by decide) (join_su (m := 159252480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 159252480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 158597120) (by decide) (join_sr (m := 151715840) (by decide) (join_su (m := 157941760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 157941760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 151715840) (by decide) (join_su (m := 159252480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 159252480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (61/320 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

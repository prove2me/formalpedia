-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u173015040_175636480_r170393600_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:37:40.39337+00:00
-- url     : https://prove2.me/submissions/e470dc7c-5e1b-4cd2-93b8-5f04c4c51f7e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/160, 67/320]`, `ρ ∈ [13/64, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 173015040 173670400 170393600 173178880 ⟨⟨83700987839, 83700987847⟩, ⟨81469499356, 85951801478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 173670400 174325760 170393600 173178880 ⟨⟨83352730919, 83352730927⟩, ⟨81128323132, 85596364522⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 173015040 173670400 173178880 175964160 ⟨⟨84970506925, 84970506933⟩, ⟨82734130840, 87226193007⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 173670400 174325760 173178880 175964160 ⟨⟨84617611331, 84617611339⟩, ⟨82388326234, 86866107583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 174325760 174981120 170393600 173178880 ⟨⟨83005934486, 83005934492⟩, ⟨80788564533, 85242431729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 174981120 175636480 170393600 173178880 ⟨⟨82660585901, 82660585904⟩, ⟨80450211326, 84889990044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 174325760 174981120 173178880 175964160 ⟨⟨84266188688, 84266188695⟩, ⟨82043951770, 86507538726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 174981120 175636480 173178880 175964160 ⟨⟨83916226292, 83916226296⟩, ⟨81700995149, 86150473317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 173015040 173670400 175964160 178749440 ⟨⟨86237627857, 86237627863⟩, ⟨83996382279, 88498168128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 173670400 174325760 175964160 178749440 ⟨⟨85880119524, 85880119531⟩, ⟨83645974964, 88133460435⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 173015040 173670400 178749440 181534720 ⟨⟨87502366923, 87502366931⟩, ⟨85256269805, 89767743294⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 173670400 174325760 178749440 181534720 ⟨⟨87140271547, 87140271555⟩, ⟨84901285219, 89398439285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 174325760 174981120 175964160 178749440 ⟨⟨85524096350, 85524096356⟩, ⟨83297010057, 87770281452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 174981120 175636480 175964160 178749440 ⟨⟨85169545567, 85169545569⟩, ⟨82949475188, 87408617998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 174325760 174981120 178749440 181534720 ⟨⟨86779673282, 86779673290⟩, ⟨84547755051, 89030675871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 174981120 175636480 178749440 181534720 ⟨⟨86420559299, 86420559303⟩, ⟨84195666872, 88664439812⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 173015040 175636480 170393600 181534720 t = true :=
  ⟨_, (join_sr (m := 175964160) (by decide) (join_su (m := 174325760) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 173670400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 173670400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 173178880) (by decide) (join_su (m := 174981120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 174981120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 174325760) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 173670400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 173670400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178749440) (by decide) (join_su (m := 174981120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 174981120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/160 : ℝ) (67/320 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e1 : (((175636480 : ℤ) : ℝ) / (D : ℝ)) = (67/320 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

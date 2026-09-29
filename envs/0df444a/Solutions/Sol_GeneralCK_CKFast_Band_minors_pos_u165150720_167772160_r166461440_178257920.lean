-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u165150720_167772160_r166461440_178257920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:47:51.148138+00:00
-- url     : https://prove2.me/submissions/a7558368-a41d-4459-b87f-18da8e7d88d2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [63/320, 1/5]`, `ρ ∈ [127/640, 17/80]` by 15 cells of the computing
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
theorem cell0 : cellOK 165150720 165806080 166461440 169410560 ⟨⟨86161006635, 86161006637⟩, ⟨83798161523, 88545376946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 165806080 166461440 166461440 169410560 ⟨⟨85800859583, 85800859591⟩, ⟨83445873169, 88177254475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 165150720 165806080 169410560 172359680 ⟨⟨87569142430, 87569142435⟩, ⟨85200903472, 89958881565⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 165806080 166461440 169410560 172359680 ⟨⟨87203877398, 87203877406⟩, ⟨84843507804, 89585631121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 166461440 167116800 166461440 169410560 ⟨⟨85442317484, 85442317492⟩, ⟨83095140095, 87810787626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 167116800 167772160 166461440 169410560 ⟨⟨85085365951, 85085365959⟩, ⟨82745948407, 87445961509⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 166461440 167116800 169410560 172359680 ⟨⟨86840231817, 86840231825⟩, ⟨84487681997, 89214050706⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 167116800 167772160 169410560 172359680 ⟨⟨86478191226, 86478191233⟩, ⟨84133412076, 88844125360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 165150720 165806080 172359680 175308800 ⟨⟨88974187784, 88974187789⟩, ⟨86600580050, 91369270501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 165806080 166461440 172359680 175308800 ⟨⟨88603838002, 88603838010⟩, ⟨86238109952, 90990925665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 165150720 166461440 175308800 178257920 ⟨⟨90188258415, 90188258423⟩, ⟨86350977569, 94081000809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 166461440 167116800 172359680 175308800 ⟨⟨88235121839, 88235121846⟩, ⟨85877223963, 90614264931⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 167116800 167772160 172359680 175308800 ⟨⟨87868024754, 87868024761⟩, ⟨85517908034, 90239273261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 166461440 167116800 175308800 178257920 ⟨⟨89627010249, 89627010257⟩, ⟨87263788453, 92011453244⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 167116800 167772160 175308800 178257920 ⟨⟨89254888900, 89254888908⟩, ⟨86899458406, 91631427817⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 165150720 167772160 166461440 178257920 t = true :=
  ⟨_, (join_sr (m := 172359680) (by decide) (join_su (m := 166461440) (by decide) (join_sr (m := 169410560) (by decide) (join_su (m := 165806080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 165806080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 169410560) (by decide) (join_su (m := 167116800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 167116800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 166461440) (by decide) (join_sr (m := 175308800) (by decide) (join_su (m := 165806080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 175308800) (by decide) (join_su (m := 167116800) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 167116800) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (63/320 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (127/640 : ℝ) (17/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  have e3 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

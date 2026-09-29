-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u158597120_159907840_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:10:42.562905+00:00
-- url     : https://prove2.me/submissions/b7c6d00a-e9b8-4cb7-a61e-da509d095959

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [121/640, 61/320]`, `ρ ∈ [1/10, 137/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 158597120 158924800 83886080 85360640 ⟨⟨47113869360, 47113869366⟩, ⟨45972078517, 48261566022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 158924800 159252480 83886080 85360640 ⟨⟨47008013039, 47008013045⟩, ⟨45868218127, 48153694955⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 158597120 158924800 85360640 86835200 ⟨⟨47900122333, 47900122339⟩, ⟨46756715484, 49049431666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 158924800 159252480 85360640 86835200 ⟨⟨47792634190, 47792634196⟩, ⟨46651226250, 48939925848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 159252480 159580160 83886080 85360640 ⟨⟨46902444489, 46902444497⟩, ⟨45764638446, 48046118821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 159580160 159907840 83886080 85360640 ⟨⟨46797162229, 46797162232⟩, ⟨45661338033, 47938836086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 159252480 159580160 85360640 86835200 ⟨⟨47685437481, 47685437487⟩, ⟨46546021381, 48830718628⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 159580160 159907840 85360640 86835200 ⟨⟨47578530705, 47578530708⟩, ⟨46441099422, 48721808458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 158597120 158924800 86835200 88309760 ⟨⟨48685284688, 48685284696⟩, ⟨47540266815, 49836201698⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 158924800 159252480 86835200 88309760 ⟨⟨48576171162, 48576171168⟩, ⟨47433155134, 49725067606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 158597120 158924800 88309760 89784320 ⟨⟨49469360988, 49469360994⟩, ⟨48322737038, 50621880706⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 158924800 159252480 88309760 89784320 ⟨⟨49358628474, 49358628480⟩, ⟨48214009271, 50509124777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 159252480 159580160 86835200 88309760 ⟨⟨48467352689, 48467352695⟩, ⟨47326331438, 49614235738⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 159580160 159907840 86835200 88309760 ⟨⟨48358827756, 48358827759⟩, ⟨47219794250, 49503704530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 159252480 159580160 88309760 89784320 ⟨⟨49248194598, 49248194604⟩, ⟨48105573068, 50396674659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 159580160 159907840 88309760 89784320 ⟨⟨49138057832, 49138057835⟩, ⟨47997426937, 50284528774⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 158597120 159907840 83886080 89784320 t = true :=
  ⟨_, (join_sr (m := 86835200) (by decide) (join_su (m := 159252480) (by decide) (join_sr (m := 85360640) (by decide) (join_su (m := 158924800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 158924800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 85360640) (by decide) (join_su (m := 159580160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 159580160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 159252480) (by decide) (join_sr (m := 88309760) (by decide) (join_su (m := 158924800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 158924800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 88309760) (by decide) (join_su (m := 159580160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 159580160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (121/640 : ℝ) (61/320 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((158597120 : ℤ) : ℝ) / (D : ℝ)) = (121/640 : ℝ) := by norm_num [D]
  have e1 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

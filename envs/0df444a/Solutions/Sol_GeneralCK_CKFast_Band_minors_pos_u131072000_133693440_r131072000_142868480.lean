-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u131072000_133693440_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:27:00.750484+00:00
-- url     : https://prove2.me/submissions/1f565e2f-e164-4ca7-b012-e6f7c1137c42

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [5/32, 51/320]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 131072000 131727360 131072000 134021120 ⟨⟨86730371013, 86730371022⟩, ⟨83948702839, 89542342498⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 131727360 132382720 131072000 134021120 ⟨⟨86338305091, 86338305098⟩, ⟨83567895505, 89138807741⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 131072000 131727360 134021120 136970240 ⟨⟨88495526162, 88495526169⟩, ⟨85707448958, 91313826628⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 131727360 132382720 134021120 136970240 ⟨⟨88096726922, 88096726929⟩, ⟨85319918025, 90903550515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 132382720 133038080 131072000 134021120 ⟨⟨85948626956, 85948626962⟩, ⟨83189384885, 88737754151⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 133038080 133693440 131072000 134021120 ⟨⟨85561310118, 85561310125⟩, ⟨82813145630, 88339154063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 132382720 133038080 134021120 136970240 ⟨⟨87700342472, 87700342477⟩, ⟨84934711042, 90495782310⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 133038080 133693440 134021120 136970240 ⟨⟨87306346142, 87306346150⟩, ⟨84551802473, 90090494173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 131072000 131727360 136970240 139919360 ⟨⟨90254624619, 90254624627⟩, ⟨87460197630, 93079194695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 131727360 132382720 136970240 139919360 ⟨⟨89849159542, 89849159549⟩, ⟨87066009774, 92662245509⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 131072000 131727360 139919360 142868480 ⟨⟨92007726216, 92007726225⟩, ⟨89207007822, 94838507405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 131727360 132382720 139919360 142868480 ⟨⟨91595661812, 91595661821⟩, ⟨88806228768, 94414952436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 132382720 133038080 136970240 139919360 ⟨⟨89446135482, 89446135484⟩, ⟨86674172337, 92247830178⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 133038080 133693440 136970240 139919360 ⟨⟨89045525596, 89045525604⟩, ⟨86284659607, 91835920710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 132382720 133038080 139919360 142868480 ⟨⟨91186063892, 91186063897⟩, ⟨88407825851, 93993956506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 133038080 133693440 139919360 142868480 ⟨⟨90778905455, 90778905464⟩, ⟨88011773191, 93575491472⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 131072000 133693440 131072000 142868480 t = true :=
  ⟨_, (join_sr (m := 136970240) (by decide) (join_su (m := 132382720) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 131727360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 131727360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 134021120) (by decide) (join_su (m := 133038080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 133038080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 132382720) (by decide) (join_sr (m := 139919360) (by decide) (join_su (m := 131727360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 131727360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 139919360) (by decide) (join_su (m := 133038080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 133038080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (5/32 : ℝ) (51/320 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e1 : (((133693440 : ℤ) : ℝ) / (D : ℝ)) = (51/320 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u173015040_175636480_r148111360_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:15:16.054606+00:00
-- url     : https://prove2.me/submissions/54ad23cc-0451-47cf-bc64-5a8658457f25

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/160, 67/320]`, `ρ ∈ [113/640, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 173015040 173670400 148111360 150896640 ⟨⟨73456503745, 73456503753⟩, ⟨71264787452, 75667661177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 173670400 174325760 148111360 150896640 ⟨⟨73146319842, 73146319850⟩, ⟨70961592109, 75350385411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 173015040 173670400 150896640 153681920 ⟨⟨74745810200, 74745810206⟩, ⟨72549055557, 76961992007⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 173670400 174325760 150896640 153681920 ⟨⟨74430771100, 74430771106⟩, ⟨72241017520, 76639849034⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 174325760 174981120 148111360 150896640 ⟨⟨72837486960, 72837486967⟩, ⟨70659704610, 75034504719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 174981120 175636480 148111360 150896640 ⟨⟨72529993106, 72529993108⟩, ⟨70359113382, 74720006678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 174325760 174981120 150896640 153681920 ⟨⟨74117097687, 74117097694⟩, ⟨71934302021, 76319115767⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 174981120 175636480 150896640 153681920 ⟨⟨73804777878, 73804777881⟩, ⟨71628897395, 75999779691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 173015040 173670400 153681920 156467200 ⟨⟨76032583448, 76032583455⟩, ⟨73830809888, 78253770046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 173670400 174325760 153681920 156467200 ⟨⟨75712717121, 75712717128⟩, ⟨73517956838, 77926788125⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 173015040 173670400 156467200 159252480 ⟨⟨77316840843, 77316840851⟩, ⟨75110067628, 79543012823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 173670400 174325760 156467200 159252480 ⟨⟨76992174994, 76992175002⟩, ⟨74792426984, 79211219947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 174325760 174981120 153681920 156467200 ⟨⟨75394230858, 75394230866⟩, ⟨73206440735, 77601230250⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 174981120 175636480 153681920 156467200 ⟨⟨75077112489, 75077112492⟩, ⟨72896249823, 77277083817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 174325760 174981120 156467200 159252480 ⟨⟨76668903303, 76668903309⟩, ⟨74476137415, 78880865163⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 174981120 175636480 156467200 159252480 ⟨⟨76347013511, 76347013515⟩, ⟨74161187077, 78551935792⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 173015040 175636480 148111360 159252480 t = true :=
  ⟨_, (join_sr (m := 153681920) (by decide) (join_su (m := 174325760) (by decide) (join_sr (m := 150896640) (by decide) (join_su (m := 173670400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 173670400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 150896640) (by decide) (join_su (m := 174981120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 174981120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 174325760) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 173670400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 173670400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 156467200) (by decide) (join_su (m := 174981120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 174981120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/160 : ℝ) (67/320 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e1 : (((175636480 : ℤ) : ℝ) / (D : ℝ)) = (67/320 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_207093760_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:26:59.516336+00:00
-- url     : https://prove2.me/submissions/43ab4be4-07e1-4bfe-ada7-16b8af9108b2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 79/320]`, `ρ ∈ [41/160, 69/256]` by 15 cells of the computing
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
theorem cell0 : cellOK 204472320 205127680 214958080 217743360 ⟨⟨85230504407, 85230504410⟩, ⟨83227976798, 87248389185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 205127680 205783040 214958080 217743360 ⟨⟨84876251147, 84876251155⟩, ⟨82879296760, 86888497964⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 204472320 205127680 217743360 220528640 ⟨⟨86268779659, 86268779661⟩, ⟨84262023096, 88290893596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205127680 205783040 217743360 220528640 ⟨⟨85910658119, 85910658126⟩, ⟨83909483952, 87927125169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 205783040 206438400 214958080 217743360 ⟨⟨84523114777, 84523114783⟩, ⟨82531705897, 86529751773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 206438400 207093760 214958080 217743360 ⟨⟨84171086889, 84171086895⟩, ⟨82185196028, 86172141984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 205783040 206438400 217743360 220528640 ⟨⟨85553660643, 85553660651⟩, ⟨83558041187, 87564508917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 206438400 207093760 217743360 220528640 ⟨⟨85197778792, 85197778800⟩, ⟨83207686585, 87203036178⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 205127680 220528640 223313920 ⟨⟨87305772725, 87305772728⟩, ⟨85294794786, 89332108145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 205127680 205783040 220528640 223313920 ⟨⟨86943797192, 86943797200⟩, ⟨84938410695, 88964476931⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 204472320 205783040 223313920 226099200 ⟨⟨88158440386, 88158440394⟩, ⟨84791916882, 91567040260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 205783040 206438400 220528640 223313920 ⟨⟨86582952765, 86582952771⟩, ⟨84583130051, 88598004898⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 206438400 207093760 220528640 223313920 ⟨⟨86223230970, 86223230976⟩, ⟨84228944607, 88232683358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 205783040 206438400 223313920 226099200 ⟨⟨87610998168, 87610998176⟩, ⟨85606979472, 89630246795⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 206438400 207093760 223313920 226099200 ⟨⟨87247450349, 87247450355⟩, ⟨85248976977, 89261090496⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 207093760 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 205783040) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 205127680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 205127680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 217743360) (by decide) (join_su (m := 206438400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 206438400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 205783040) (by decide) (join_sr (m := 223313920) (by decide) (join_su (m := 205127680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 223313920) (by decide) (join_su (m := 206438400) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 206438400) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (79/320 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((207093760 : ℤ) : ℝ) / (D : ℝ)) = (79/320 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

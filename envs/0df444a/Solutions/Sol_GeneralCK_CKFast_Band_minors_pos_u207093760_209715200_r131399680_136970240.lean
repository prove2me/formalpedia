-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u207093760_209715200_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:51:19.072175+00:00
-- url     : https://prove2.me/submissions/61a984ac-7b5e-423d-819b-0f581d2c603d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [79/320, 1/4]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 207093760 207749120 131399680 132792320 ⟨⟨52263366312, 52263366319⟩, ⟨50719362058, 53817535312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 207093760 207749120 132792320 134184960 ⟨⟨52795224971, 52795224978⟩, ⟨51249210650, 54351408039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 207749120 208404480 131399680 132792320 ⟨⟨52036724504, 52036724505⟩, ⟨50496364906, 53587207766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 207749120 208404480 132792320 134184960 ⟨⟨52566427499, 52566427502⟩, ⟨51024063422, 54118919299⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 207093760 207749120 134184960 135577600 ⟨⟨53326719776, 53326719783⟩, ⟨51778696938, 54884915340⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 207093760 207749120 135577600 136970240 ⟨⟨53857851743, 53857851750⟩, ⟨52307821934, 55418058239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 207749120 208404480 134184960 135577600 ⟨⟨53095770947, 53095770950⟩, ⟨51551403909, 54650269743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 207749120 208404480 135577600 136970240 ⟨⟨53624755846, 53624755848⟩, ⟨52078387363, 55181260105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 208404480 209059840 131399680 132792320 ⟨⟨51810884514, 51810884521⟩, ⟨50274149309, 53357702622⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 208404480 209059840 132792320 134184960 ⟨⟨52338437713, 52338437720⟩, ⟨50799703606, 53887258838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 209059840 209715200 131399680 132792320 ⟨⟨51585839868, 51585839875⟩, ⟨50052708955, 53129013224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 209059840 209715200 132792320 134184960 ⟨⟨52111249100, 52111249105⟩, ⟨50576124846, 53656419962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 208404480 209059840 134184960 135577600 ⟨⟨52865635626, 52865635632⟩, ⟨51324904101, 54416458257⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 208404480 209059840 135577600 136970240 ⟨⟨53392479235, 53392479240⟩, ⟨51849751779, 54945301871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 209059840 209715200 134184960 135577600 ⟨⟨52636307260, 52636307265⟩, ⟨51099191123, 54183474150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 209059840 209715200 135577600 136970240 ⟨⟨53161015318, 53161015323⟩, ⟨51621908753, 54710176766⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 207093760 209715200 131399680 136970240 t = true :=
  ⟨_, (join_su (m := 208404480) (by decide) (join_sr (m := 134184960) (by decide) (join_su (m := 207749120) (by decide) (join_sr (m := 132792320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 132792320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 207749120) (by decide) (join_sr (m := 135577600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 135577600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 134184960) (by decide) (join_su (m := 209059840) (by decide) (join_sr (m := 132792320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 132792320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 209059840) (by decide) (join_sr (m := 135577600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 135577600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (79/320 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((207093760 : ℤ) : ℝ) / (D : ℝ)) = (79/320 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

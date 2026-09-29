-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_235929600_r460062720_482344960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:17:08.863971+00:00
-- url     : https://prove2.me/submissions/fea88d23-de5d-48c5-a8db-8231fe69ea39

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 9/32]`, `ρ ∈ [351/640, 23/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231997440 460062720 465633280 ⟨⟨147508206970, 147508206978⟩, ⟨143269517701, 151800856329⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 231997440 233308160 460062720 465633280 ⟨⟨146304580342, 146304580344⟩, ⟨142086590406, 150576249612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 230686720 231997440 465633280 471203840 ⟨⟨149167625034, 149167625041⟩, ⟨144914487182, 153474739199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231997440 233308160 465633280 471203840 ⟨⟨147952236700, 147952236703⟩, ⟨143719831984, 152238340079⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 233308160 234618880 460062720 465633280 ⟨⟨145105176916, 145105176924⟩, ⟨140907750443, 149356003823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 234618880 235929600 460062720 465633280 ⟨⟨143909945493, 143909945501⟩, ⟨139732948075, 148140066270⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233308160 234618880 465633280 471203840 ⟨⟨146741071968, 146741071974⟩, ⟨142529265470, 151006301262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 234618880 235929600 465633280 471203840 ⟨⟨145534079798, 145534079806⟩, ⟨141342738046, 149778570245⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 230686720 231997440 471203840 476774400 ⟨⟨150825044020, 150825044027⟩, ⟨146557472362, 155146607127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231997440 233308160 471203840 476774400 ⟨⟨149597937686, 149597937689⟩, ⟨145351132206, 153898460088⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 230686720 231997440 476774400 482344960 ⟨⟨152480486629, 152480486637⟩, ⟨148198495720, 156816483035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 231997440 233308160 476774400 482344960 ⟨⟨151241705423, 151241705427⟩, ⟨146980512981, 155556631972⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 233308160 234618880 471203840 476774400 ⟨⟨148375054669, 148375054677⟩, ⟨144148881418, 152654672032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 234618880 235929600 471203840 476774400 ⟨⟨147156344102, 147156344109⟩, ⟨142950670551, 151415190649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 233308160 234618880 476774400 482344960 ⟨⟨150007146578, 150007146585⟩, ⟨145766619636, 154301137889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 234618880 235929600 476774400 482344960 ⟨⟨148776759402, 148776759410⟩, ⟨144556766392, 153049948677⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 235929600 460062720 482344960 t = true :=
  ⟨_, (join_sr (m := 471203840) (by decide) (join_su (m := 233308160) (by decide) (join_sr (m := 465633280) (by decide) (join_su (m := 231997440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 231997440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 465633280) (by decide) (join_su (m := 234618880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 234618880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 233308160) (by decide) (join_sr (m := 476774400) (by decide) (join_su (m := 231997440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 231997440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 476774400) (by decide) (join_su (m := 234618880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 234618880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (351/640 : ℝ) (23/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  have e3 : (((482344960 : ℤ) : ℝ) / (D : ℝ)) = (23/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

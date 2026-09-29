-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_246415360_r460062720_482344960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:20:05.723789+00:00
-- url     : https://prove2.me/submissions/54f882f1-fb77-4b18-ab8e-8cdd53d8d869

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 47/160]`, `ρ ∈ [351/640, 23/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 242483200 460062720 465633280 ⟨⟨137994618166, 137994618173⟩, ⟨133917800141, 142123201111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 242483200 243793920 460062720 465633280 ⟨⟨136823376748, 136823376756⟩, ⟨132766211193, 140932040826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241172480 242483200 465633280 471203840 ⟨⟨139559962504, 139559962511⟩, ⟨135468991874, 143702737305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242483200 243793920 465633280 471203840 ⟨⟨138376966842, 138376966850⟩, ⟨134305689543, 142499784519⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243793920 245104640 460062720 465633280 ⟨⟨135655965335, 135655965343⟩, ⟨131618327613, 139744836914⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 245104640 246415360 460062720 465633280 ⟨⟨134492337296, 134492337298⟩, ⟨130474104087, 138561541407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 243793920 245104640 465633280 471203840 ⟨⟨137197802745, 137197802751⟩, ⟨133146094933, 141300788811⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 245104640 246415360 465633280 471203840 ⟨⟨136022423701, 136022423704⟩, ⟨131990162834, 140105702359⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 241172480 242483200 471203840 476774400 ⟨⟨141123638669, 141123638676⟩, ⟨137018524480, 145280595338⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 242483200 243793920 471203840 476774400 ⟨⟨139928927193, 139928927200⟩, ⟨135843546536, 144065889158⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 241172480 242483200 476774400 482344960 ⟨⟨142685665052, 142685665060⟩, ⟨138566416195, 146856793759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 242483200 243793920 476774400 482344960 ⟨⟨141479275704, 141479275712⟩, ⟨137379799923, 145630372798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243793920 245104640 471203840 476774400 ⟨⟨138738048208, 138738048216⟩, ⟨134672278046, 142855140122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245104640 246415360 471203840 476774400 ⟨⟨137550955337, 137550955341⟩, ⟨133504673913, 141648300554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 243793920 245104640 476774400 482344960 ⟨⟨140276719156, 140276719162⟩, ⟨136196894234, 144407908416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245104640 246415360 476774400 482344960 ⟨⟨139077949163, 139077949167⟩, ⟨135017654143, 143189353089⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 246415360 460062720 482344960 t = true :=
  ⟨_, (join_sr (m := 471203840) (by decide) (join_su (m := 243793920) (by decide) (join_sr (m := 465633280) (by decide) (join_su (m := 242483200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 242483200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 465633280) (by decide) (join_su (m := 245104640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 245104640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 243793920) (by decide) (join_sr (m := 476774400) (by decide) (join_su (m := 242483200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 242483200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 476774400) (by decide) (join_su (m := 245104640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 245104640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (351/640 : ℝ) (23/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  have e3 : (((482344960 : ℤ) : ℝ) / (D : ℝ)) = (23/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

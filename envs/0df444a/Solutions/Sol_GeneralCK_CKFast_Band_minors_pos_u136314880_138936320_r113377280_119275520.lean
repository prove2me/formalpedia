-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_138936320_r113377280_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:18:36.363056+00:00
-- url     : https://prove2.me/submissions/1ec14355-e24d-4162-9a3b-b9d580872600

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 53/320]`, `ρ ∈ [173/1280, 91/640]` by 8 cells of the computing
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
theorem cell0 : cellOK 136314880 136970240 113377280 116326400 ⟨⟨73267714006, 73267714015⟩, ⟨70612735341, 75951777640⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136970240 137625600 113377280 116326400 ⟨⟨72934505165, 72934505173⟩, ⟨70290002866, 75607890943⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 136314880 136970240 116326400 119275520 ⟨⟨75014116905, 75014116913⟩, ⟨72352478465, 77704773954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 136970240 137625600 116326400 119275520 ⟨⟨74673998006, 74673998015⟩, ⟨72022852030, 77353962573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 137625600 138280960 113377280 116326400 ⟨⟨72603313661, 72603313668⟩, ⟨69969204398, 75266107123⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 138280960 138936320 113377280 116326400 ⟨⟨72274117179, 72274117186⟩, ⟨69650318652, 74926402803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 137625600 138280960 116326400 119275520 ⟨⟨74335926557, 74335926566⟩, ⟨71695189828, 77005284035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 138280960 138936320 116326400 119275520 ⟨⟨73999880008, 73999880017⟩, ⟨71369470341, 76658714735⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 138936320 113377280 119275520 t = true :=
  ⟨_, (join_su (m := 137625600) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 136970240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 136970240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 116326400) (by decide) (join_su (m := 138280960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 138280960) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (53/320 : ℝ) →
    rho ∈ Set.Icc (173/1280 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((138936320 : ℤ) : ℝ) / (D : ℝ)) = (53/320 : ℝ) := by norm_num [D]
  have e2 : (((113377280 : ℤ) : ℝ) / (D : ℝ)) = (173/1280 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

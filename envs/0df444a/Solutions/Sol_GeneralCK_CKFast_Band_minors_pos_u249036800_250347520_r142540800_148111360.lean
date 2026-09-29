-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_250347520_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:56:43.031634+00:00
-- url     : https://prove2.me/submissions/49a99202-6c72-4050-ae7c-3f565941befd

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 191/640]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249364480 142540800 143933440 ⟨⟨42419546718, 42419546724⟩, ⟨41626194845, 43215769487⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249364480 249692160 142540800 143933440 ⟨⟨42318961147, 42318961152⟩, ⟨41526568797, 43114218816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249036800 249364480 143933440 145326080 ⟨⟨42822979955, 42822979961⟩, ⟨42028722873, 43620109445⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249364480 249692160 143933440 145326080 ⟨⟨42721477914, 42721477919⟩, ⟨41928181773, 43517640889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249692160 250019840 142540800 143933440 ⟨⟨42218505700, 42218505703⟩, ⟨41427070810, 43012800346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 250019840 250347520 142540800 143933440 ⟨⟨42118179886, 42118179891⟩, ⟨41327700400, 42911513589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249692160 250019840 143933440 145326080 ⟨⟨42620106916, 42620106919⟩, ⟨41827769652, 43415305457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 250019840 250347520 143933440 145326080 ⟨⟨42518866469, 42518866474⟩, ⟨41727486023, 43313102655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 249364480 145326080 146718720 ⟨⟨43226253109, 43226253114⟩, ⟨42431091027, 44024289107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249364480 249692160 145326080 146718720 ⟨⟨43123835669, 43123835674⟩, ⟨42329635944, 43920903744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 249036800 249364480 146718720 148111360 ⟨⟨43629366536, 43629366541⟩, ⟨42833299662, 44428308832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 249364480 249692160 146718720 148111360 ⟨⟨43526034768, 43526034774⟩, ⟨42730931660, 44324007736⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249692160 250019840 145326080 146718720 ⟨⟨43021550188, 43021550190⟩, ⟨42228310751, 43817652419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250019840 250347520 145326080 146718720 ⟨⟨42919396168, 42919396173⟩, ⟨42127114959, 43714534639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 249692160 250019840 146718720 148111360 ⟨⟨43422835867, 43422835870⟩, ⟨42628694456, 44219841586⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250019840 250347520 146718720 148111360 ⟨⟨43319769331, 43319769337⟩, ⟨42526587557, 44115809888⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 250347520 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 249692160) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 249364480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 249364480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 250019840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 250019840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 249692160) (by decide) (join_sr (m := 146718720) (by decide) (join_su (m := 249364480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 249364480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 146718720) (by decide) (join_su (m := 250019840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 250019840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (191/640 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((250347520 : ℤ) : ℝ) / (D : ℝ)) = (191/640 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_225443840_r571473920_593756160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:44:57.390382+00:00
-- url     : https://prove2.me/submissions/b8fcc2fb-8779-43a5-92b6-832fb21ec628

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 43/160]`, `ρ ∈ [109/160, 453/640]` by 11 cells of the computing
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
theorem cell0 : cellOK 220200960 222822400 571473920 577044480 ⟨⟨191211917581, 191211917590⟩, ⟨183136633446, 199449991357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 222822400 577044480 582615040 ⟨⟨192917568049, 192917568058⟩, ⟨184815213857, 201182716994⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 224133120 571473920 577044480 ⟨⟨189018203290, 189018203299⟩, ⟨184363186604, 193728597925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 224133120 225443840 571473920 577044480 ⟨⟨187561309800, 187561309809⟩, ⟨182928244869, 192249534229⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 222822400 224133120 577044480 582615040 ⟨⟨190707499517, 190707499526⟩, ⟨186038192836, 195432156011⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 224133120 225443840 577044480 582615040 ⟨⟨189239686755, 189239686763⟩, ⟨184592344641, 193942164081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 220200960 222822400 582615040 588185600 ⟨⟨194621384762, 194621384770⟩, ⟨186491980856, 202913584257⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 220200960 222822400 588185600 593756160 ⟨⟨196323391798, 196323391807⟩, ⟨188166958128, 204642617607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 222822400 224133120 582615040 588185600 ⟨⟨192395016853, 192395016862⟩, ⟨187711434436, 197133919706⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 224133120 225443840 582615040 588185600 ⟨⟨190916320783, 190916320791⟩, ⟨186254715099, 195633036163⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 222822400 225443840 588185600 593756160 ⟨⟨193335457585, 193335457594⟩, ⟨185243450098, 201589393097⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 225443840 571473920 593756160 t = true :=
  ⟨_, (join_sr (m := 582615040) (by decide) (join_su (m := 222822400) (by decide) (join_sr (m := 577044480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 577044480) (by decide) (join_su (m := 224133120) (by decide) (leaf_ok cell2) (leaf_ok cell3)) (join_su (m := 224133120) (by decide) (leaf_ok cell4) (leaf_ok cell5)))) (join_su (m := 222822400) (by decide) (join_sr (m := 588185600) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 588185600) (by decide) (join_su (m := 224133120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (109/160 : ℝ) (453/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((571473920 : ℤ) : ℝ) / (D : ℝ)) = (109/160 : ℝ) := by norm_num [D]
  have e3 : (((593756160 : ℤ) : ℝ) / (D : ℝ)) = (453/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

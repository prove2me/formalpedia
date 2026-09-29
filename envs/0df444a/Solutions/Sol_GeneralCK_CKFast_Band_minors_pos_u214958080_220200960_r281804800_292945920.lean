-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_220200960_r281804800_292945920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:45:56.61398+00:00
-- url     : https://prove2.me/submissions/c131b7aa-4541-4e4b-9d0c-8e965ae55f85

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 21/80]`, `ρ ∈ [43/128, 447/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 214958080 216268800 281804800 284590080 ⟨⟨102649256180, 102649256188⟩, ⟨99250937519, 106087887680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 214958080 216268800 284590080 287375360 ⟨⟨103600605559, 103600605567⟩, ⟨100194975094, 107046571412⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 216268800 217579520 281804800 284590080 ⟨⟨101802888116, 101802888124⟩, ⟨98419892007, 105225947114⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 216268800 217579520 284590080 287375360 ⟨⟨102747276172, 102747276178⟩, ⟨99356992686, 106177646140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 214958080 216268800 287375360 290160640 ⟨⟨104551021021, 104551021028⟩, ⟨101138085652, 108004314061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 214958080 216268800 290160640 292945920 ⟨⟨105500507628, 105500507635⟩, ⟨102080274215, 108961120730⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 216268800 217579520 287375360 290160640 ⟨⟨103690750949, 103690750957⟩, ⟨100293186698, 107128425020⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 216268800 217579520 290160640 292945920 ⟨⟨104633317374, 104633317380⟩, ⟨101228478928, 108078288716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 217579520 218890240 281804800 284590080 ⟨⟨100960956615, 100960956623⟩, ⟨97593141265, 104368587806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 217579520 218890240 284590080 287375360 ⟨⟨101898399892, 101898399899⟩, ⟨98523321838, 105313318405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 218890240 220200960 281804800 284590080 ⟨⟨100123400168, 100123400172⟩, ⟨96770625781, 103515746204⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 218890240 220200960 284590080 287375360 ⟨⟨101053915120, 101053915124⟩, ⟨97693902935, 104453524567⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 217579520 218890240 287375360 290160640 ⟨⟨102834950170, 102834950177⟩, ⟨99452615736, 106257149425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 217579520 218890240 290160640 292945920 ⟨⟨103770612234, 103770612241⟩, ⟨100381027709, 107200085688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 218890240 220200960 287375360 290160640 ⟨⟨101983556993, 101983556995⟩, ⟨98616313055, 105390423553⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 218890240 220200960 290160640 292945920 ⟨⟨102912330435, 102912330438⟩, ⟨99537860755, 106326447852⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 220200960 281804800 292945920 t = true :=
  ⟨_, (join_su (m := 217579520) (by decide) (join_sr (m := 287375360) (by decide) (join_su (m := 216268800) (by decide) (join_sr (m := 284590080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 284590080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 216268800) (by decide) (join_sr (m := 290160640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 290160640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 287375360) (by decide) (join_su (m := 218890240) (by decide) (join_sr (m := 284590080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 284590080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 218890240) (by decide) (join_sr (m := 290160640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 290160640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (43/128 : ℝ) (447/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  have e3 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_41943040_r232652800_256901120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:51:09.775779+00:00
-- url     : https://prove2.me/submissions/252ff611-7cc0-405e-a45b-bde4e20e3999

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 1/20]`, `ρ ∈ [71/256, 49/160]` by 8 cells of the computing
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
theorem cell0 : cellOK 33554432 35651584 232652800 244776960 ⟨⟨298545463501, 298545463521⟩, ⟨275403910866, 322757055263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 35651584 37748736 232652800 244776960 ⟨⟨292670674537, 292670674556⟩, ⟨270098779063, 316278940294⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 33554432 35651584 244776960 256901120 ⟨⟨307583550697, 307583550715⟩, ⟨284665172205, 331509077481⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 35651584 37748736 244776960 256901120 ⟨⟨301699366903, 301699366918⟩, ⟨279327868761, 325048333780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 37748736 39845888 232652800 244776960 ⟨⟨287018410186, 287018410204⟩, ⟨264988733777, 310052231589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 39845888 41943040 232652800 244776960 ⟨⟨281573965267, 281573965285⟩, ⟨260061148696, 304060085957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 37748736 39845888 244776960 256901120 ⟨⟨296031247492, 296031247510⟩, ⟨274181062253, 318830370940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 39845888 41943040 244776960 256901120 ⟨⟨290565190952, 290565190969⟩, ⟨269212652754, 312839252235⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 41943040 232652800 256901120 t = true :=
  ⟨_, (join_su (m := 37748736) (by decide) (join_sr (m := 244776960) (by decide) (join_su (m := 35651584) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 35651584) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 244776960) (by decide) (join_su (m := 39845888) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 39845888) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (1/20 : ℝ) →
    rho ∈ Set.Icc (71/256 : ℝ) (49/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e2 : (((232652800 : ℤ) : ℝ) / (D : ℝ)) = (71/256 : ℝ) := by norm_num [D]
  have e3 : (((256901120 : ℤ) : ℝ) / (D : ℝ)) = (49/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

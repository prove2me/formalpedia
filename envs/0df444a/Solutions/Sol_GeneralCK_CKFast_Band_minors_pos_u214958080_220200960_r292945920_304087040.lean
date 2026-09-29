-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_220200960_r292945920_304087040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:46:04.445642+00:00
-- url     : https://prove2.me/submissions/a6a8f3f8-7117-4ff0-9c0b-ce4c8a889615

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 21/80]`, `ρ ∈ [447/1280, 29/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 214958080 216268800 292945920 295731200 ⟨⟨106449070418, 106449070425⟩, ⟨103021545781, 109916996498⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 214958080 216268800 295731200 298516480 ⟨⟨107396714406, 107396714414⟩, ⟨103961905325, 110871946422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 216268800 217579520 292945920 295731200 ⟨⟨105574980342, 105574980350⟩, ⟨102162874235, 109027242165⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 216268800 217579520 295731200 298516480 ⟨⟨106515744732, 106515744739⟩, ⟨103096377457, 109975290283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 214958080 216268800 298516480 301301760 ⟨⟨108343444586, 108343444594⟩, ⟨104901357799, 111825975534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 214958080 216268800 301301760 304087040 ⟨⟨109289265927, 109289265933⟩, ⟨105839908132, 112779088842⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 216268800 217579520 298516480 301301760 ⟨⟨107455615399, 107455615406⟩, ⟨104028993409, 110922437961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 216268800 217579520 301301760 304087040 ⟨⟨108394597175, 108394597181⟩, ⟨104960726889, 111868690072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 217579520 218890240 292945920 295731200 ⟨⟨104705390847, 104705390854⟩, ⟨101308562482, 108142131995⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 217579520 218890240 295731200 298516480 ⟨⟨105639290751, 105639290758⟩, ⟨102235224759, 109083293125⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 218890240 220200960 292945920 295731200 ⟨⟨103840240081, 103840240084⟩, ⟨100458550632, 107261602130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 218890240 220200960 295731200 298516480 ⟨⟨104767290537, 104767290540⟩, ⟨101378387262, 108195891028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 217579520 218890240 298516480 301301760 ⟨⟨106572316666, 106572316674⟩, ⟨103161019225, 110023573835⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 217579520 218890240 301301760 304087040 ⟨⟨107504473293, 107504473300⟩, ⟨104085950545, 110962978858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 218890240 220200960 298516480 301301760 ⟨⟨105693486397, 105693486400⟩, ⟨102297375198, 109129319174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 218890240 220200960 301301760 304087040 ⟨⟨106618832227, 106618832229⟩, ⟨103215518976, 110061891172⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 220200960 292945920 304087040 t = true :=
  ⟨_, (join_su (m := 217579520) (by decide) (join_sr (m := 298516480) (by decide) (join_su (m := 216268800) (by decide) (join_sr (m := 295731200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 295731200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 216268800) (by decide) (join_sr (m := 301301760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 301301760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 298516480) (by decide) (join_su (m := 218890240) (by decide) (join_sr (m := 295731200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 295731200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 218890240) (by decide) (join_sr (m := 301301760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 301301760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (447/1280 : ℝ) (29/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  have e3 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

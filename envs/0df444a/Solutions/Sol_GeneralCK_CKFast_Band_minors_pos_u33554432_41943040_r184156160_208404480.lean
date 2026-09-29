-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_41943040_r184156160_208404480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:49:15.585214+00:00
-- url     : https://prove2.me/submissions/0d5374cd-77a4-44e9-91e0-730151046804

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 1/20]`, `ρ ∈ [281/1280, 159/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 33554432 35651584 184156160 190218240 ⟨⟨256841725470, 256841725486⟩, ⟨238992518108, 275460801448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 33554432 35651584 190218240 196280320 ⟨⟨262065185152, 262065185171⟩, ⟨244293636480, 280583148342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 35651584 37748736 184156160 190218240 ⟨⟨251077714472, 251077714487⟩, ⟨233726472479, 269168273160⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 35651584 37748736 190218240 196280320 ⟨⟨256280376670, 256280376685⟩, ⟨238996277988, 274282165900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 33554432 35651584 196280320 202342400 ⟨⟨267195697109, 267195697125⟩, ⟨249501590662, 285613678792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 33554432 35651584 202342400 208404480 ⟨⟨272237458156, 272237458176⟩, ⟨254620475106, 290556644255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 35651584 37748736 196280320 202342400 ⟨⟨261392560145, 261392560164⟩, ⟨244175674595, 279306316720⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 35651584 37748736 202342400 208404480 ⟨⟨266418254270, 266418254289⟩, ⟨249268543044, 284244783455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 37748736 39845888 184156160 190218240 ⟨⟨245565679459, 245565679474⟩, ⟨228684207800, 263157716163⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 37748736 39845888 190218240 196280320 ⟨⟨250743962107, 250743962125⟩, ⟨233920154913, 268258366404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 39845888 41943040 184156160 190218240 ⟨⟨240287245328, 240287245343⟩, ⟨223849763820, 257408213558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 39845888 41943040 190218240 196280320 ⟨⟨245438061322, 245438061341⟩, ⟨229049685834, 262491462789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 37748736 39845888 196280320 202342400 ⟨⟨255834252832, 255834252847⟩, ⟨239068417670, 273271429292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 37748736 39845888 202342400 208404480 ⟨⟨260840341327, 260840341345⟩, ⟨244132673383, 278200773101⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 39845888 41943040 196280320 202342400 ⟨⟨250503372119, 250503372137⟩, ⟨234164606889, 267489332052⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 39845888 41943040 202342400 208404480 ⟨⟨255486775931, 255486775946⟩, ⟨239198011015, 272405505268⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 41943040 184156160 208404480 t = true :=
  ⟨_, (join_su (m := 37748736) (by decide) (join_sr (m := 196280320) (by decide) (join_su (m := 35651584) (by decide) (join_sr (m := 190218240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 190218240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 35651584) (by decide) (join_sr (m := 202342400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 202342400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 196280320) (by decide) (join_su (m := 39845888) (by decide) (join_sr (m := 190218240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 190218240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 39845888) (by decide) (join_sr (m := 202342400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 202342400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (1/20 : ℝ) →
    rho ∈ Set.Icc (281/1280 : ℝ) (159/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e2 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  have e3 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

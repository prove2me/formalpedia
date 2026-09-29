-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_25165824_r184156160_208404480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:27:47.687085+00:00
-- url     : https://prove2.me/submissions/ee07db99-6bca-4bcf-850b-3ce84245bf4d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 3/100]`, `ρ ∈ [281/1280, 159/640]` by 13 cells of the computing
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
theorem cell0 : cellOK 16777216 18874368 184156160 190218240 ⟨⟨315180523375, 315180523395⟩, ⟨291887399559, 339567843087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 16777216 18874368 190218240 196280320 ⟨⟨320346868873, 320346868898⟩, ⟨297275019859, 344465238864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 18874368 20971520 184156160 190218240 ⟨⟨306366434084, 306366434108⟩, ⟨283945875241, 329832171671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 18874368 20971520 190218240 196280320 ⟨⟨311572303050, 311572303074⟩, ⟨289346764777, 334799690051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 16777216 18874368 196280320 208404480 ⟨⟨327896223600, 327896223620⟩, ⟨297161259861, 360432121339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 18874368 20971520 196280320 208404480 ⟨⟨319182411297, 319182411321⟩, ⟨289533172911, 350555669345⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 20971520 23068672 184156160 190218240 ⟨⟨298078334306, 298078334325⟩, ⟨276460968997, 320694222620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 20971520 23068672 190218240 196280320 ⟨⟨303311437798, 303311437821⟩, ⟨281865935537, 325715994181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 23068672 25165824 184156160 190218240 ⟨⟨290261644390, 290261644411⟩, ⟨269387139038, 312090547279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 23068672 25165824 190218240 196280320 ⟨⟨295511552280, 295511552303⟩, ⟨274788401481, 317153073835⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 20971520 23068672 196280320 208404480 ⟨⟨310964735493, 310964735511⟩, ⟨282321696601, 341258764741⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 23068672 25165824 196280320 202342400 ⟨⟨300657444891, 300657444910⟩, ⟨280082887500, 322116104930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 23068672 25165824 202342400 208404480 ⟨⟨305704632865, 305704632887⟩, ⟨285275905024, 326984838569⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 25165824 184156160 208404480 t = true :=
  ⟨_, (join_su (m := 20971520) (by decide) (join_sr (m := 196280320) (by decide) (join_su (m := 18874368) (by decide) (join_sr (m := 190218240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 190218240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 18874368) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 196280320) (by decide) (join_su (m := 23068672) (by decide) (join_sr (m := 190218240) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 190218240) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 23068672) (by decide) (leaf_ok cell10) (join_sr (m := 202342400) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (3/100 : ℝ) →
    rho ∈ Set.Icc (281/1280 : ℝ) (159/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e2 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  have e3 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

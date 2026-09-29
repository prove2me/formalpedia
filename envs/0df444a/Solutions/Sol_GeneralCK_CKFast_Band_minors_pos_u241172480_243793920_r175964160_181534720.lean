-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_243793920_r175964160_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:00:43.379664+00:00
-- url     : https://prove2.me/submissions/2e1e109f-545c-4eee-b07b-2fb704342e05

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 93/320]`, `ρ ∈ [537/2560, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 241827840 175964160 177356800 ⟨⟨54977056901, 54977056906⟩, ⟨53543627539, 56419050625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241172480 241827840 177356800 178749440 ⟨⟨55397928798, 55397928805⟩, ⟨53962774953, 56841652652⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241827840 242483200 175964160 177356800 ⟨⟨54725232243, 54725232249⟩, ⟨53294733464, 56164267771⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 241827840 242483200 177356800 178749440 ⟨⟨55144283566, 55144283572⟩, ⟨53712064769, 56585044784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241172480 241827840 178749440 180142080 ⟨⟨55818623852, 55818623858⟩, ⟨54381745863, 57264077484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 241172480 241827840 180142080 181534720 ⟨⟨56239142476, 56239142482⟩, ⟨54800540686, 57686325535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 241827840 242483200 178749440 180142080 ⟨⟨55563160309, 55563160315⟩, ⟨54129221821, 57005646881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 241827840 242483200 180142080 181534720 ⟨⟨55981862878, 55981862883⟩, ⟨54546205025, 57426074469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 242483200 243138560 175964160 177356800 ⟨⟨54474061966, 54474061971⟩, ⟨53046479998, 55910153241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 242483200 243138560 177356800 178749440 ⟨⟨54891296078, 54891296084⟩, ⟨53461998553, 56329108612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243138560 243793920 175964160 177356800 ⟨⟨54223541274, 54223541281⟩, ⟨52798862445, 55656702144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 243138560 243793920 177356800 178749440 ⟨⟨54638961522, 54638961527⟩, ⟨53212571590, 56073839221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 242483200 243138560 178749440 180142080 ⟨⟨55308357851, 55308357856⟩, ⟨53877345081, 56747891319⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 242483200 243138560 180142080 181534720 ⟨⟨55725247684, 55725247689⟩, ⟨54292519982, 57166501764⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 243138560 243793920 178749440 180142080 ⟨⟨55054211645, 55054211650⟩, ⟨53626110909, 56490805865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 243138560 243793920 180142080 181534720 ⟨⟨55469292039, 55469292045⟩, ⟨54039480800, 56907602473⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 243793920 175964160 181534720 t = true :=
  ⟨_, (join_su (m := 242483200) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 241827840) (by decide) (join_sr (m := 177356800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 177356800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 241827840) (by decide) (join_sr (m := 180142080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 180142080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 178749440) (by decide) (join_su (m := 243138560) (by decide) (join_sr (m := 177356800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 177356800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 243138560) (by decide) (join_sr (m := 180142080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 180142080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (537/2560 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((175964160 : ℤ) : ℝ) / (D : ℝ)) = (537/2560 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

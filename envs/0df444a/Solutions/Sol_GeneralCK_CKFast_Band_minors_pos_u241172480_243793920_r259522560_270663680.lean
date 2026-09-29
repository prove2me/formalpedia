-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_243793920_r259522560_270663680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:15:40.885727+00:00
-- url     : https://prove2.me/submissions/ccb73ae4-729e-45a0-bc8d-9c27268ee210

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 93/320]`, `ρ ∈ [99/320, 413/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 241827840 259522560 262307840 ⟨⟨80135630375, 80135630382⟩, ⟨78349078684, 81934636417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241827840 242483200 259522560 262307840 ⟨⟨79777513392, 79777513398⟩, ⟨77995416275, 81572021173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241172480 241827840 262307840 265093120 ⟨⟨80957257171, 80957257177⟩, ⟨79167047276, 82759930341⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 241827840 242483200 262307840 265093120 ⟨⟨80595752415, 80595752422⟩, ⟨78810005828, 82393918711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 242483200 243138560 259522560 262307840 ⟨⟨79420215436, 79420215441⟩, ⟨77642554733, 81210243358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 243138560 243793920 259522560 262307840 ⟨⟨79063730847, 79063730854⟩, ⟨77290488517, 80849297190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 242483200 243138560 262307840 265093120 ⟨⟨80235070887, 80235070892⟩, ⟨78453769454, 82028748698⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 243138560 243793920 262307840 265093120 ⟨⟨79875206907, 79875206914⟩, ⟨78098332603, 81664414500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 241172480 241827840 265093120 267878400 ⟨⟨81778272652, 81778272659⟩, ⟨79984406527, 83584610924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 241827840 242483200 265093120 267878400 ⟨⟨81413387692, 81413387698⟩, ⟨79623993544, 83215210538⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 241172480 241827840 267878400 270663680 ⟨⟨82598679762, 82598679767⟩, ⟨80801159368, 84408681119⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 241827840 242483200 267878400 270663680 ⟨⟨82230422120, 82230422125⟩, ⟨80437382312, 84035899564⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 242483200 243138560 265093120 267878400 ⟨⟨81049330085, 81049330092⟩, ⟨79264389775, 82846655882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243138560 243793920 265093120 267878400 ⟨⟨80686094139, 80686094144⟩, ⟨78905589648, 82478941140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 242483200 243138560 267878400 270663680 ⟨⟨81862995887, 81862995892⟩, ⟨80074418538, 83663967779⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 243138560 243793920 267878400 270663680 ⟨⟨81496395350, 81496395357⟩, ⟨79712262455, 83292879930⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 243793920 259522560 270663680 t = true :=
  ⟨_, (join_sr (m := 265093120) (by decide) (join_su (m := 242483200) (by decide) (join_sr (m := 262307840) (by decide) (join_su (m := 241827840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 241827840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 262307840) (by decide) (join_su (m := 243138560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 243138560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 242483200) (by decide) (join_sr (m := 267878400) (by decide) (join_su (m := 241827840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 241827840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 267878400) (by decide) (join_su (m := 243138560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 243138560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (99/320 : ℝ) (413/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  have e3 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

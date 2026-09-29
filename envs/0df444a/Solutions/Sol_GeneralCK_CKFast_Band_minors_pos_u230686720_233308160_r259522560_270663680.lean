-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_233308160_r259522560_270663680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:05:33.077966+00:00
-- url     : https://prove2.me/submissions/26d9b97b-2ca1-468b-85d5-4cadf3eb2724

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 89/320]`, `ρ ∈ [99/320, 413/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231342080 259522560 262307840 ⟨⟨85981671504, 85981671506⟩, ⟨84121272844, 87855257690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 231342080 231997440 259522560 262307840 ⟨⟨85609645668, 85609645675⟩, ⟨83754009660, 87478421416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 230686720 231342080 262307840 265093120 ⟨⟨86858088838, 86858088842⟩, ⟨84993894147, 88735477826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231342080 231997440 262307840 265093120 ⟨⟨86482605534, 86482605540⟩, ⟨84623181988, 88355175739⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 231997440 232652800 259522560 262307840 ⟨⟨85238535282, 85238535288⟩, ⟨83387641660, 87102521127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 232652800 233308160 259522560 262307840 ⟨⟨84868333975, 84868333980⟩, ⟨83022162612, 86727550310⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231997440 232652800 262307840 265093120 ⟨⟨86108042172, 86108042179⟩, ⟨84253369523, 87975814112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 232652800 233308160 262307840 265093120 ⟨⟨85734392364, 85734392370⟩, ⟨83884450504, 87597386411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 230686720 231342080 265093120 267878400 ⟨⟨87733763399, 87733763403⟩, ⟨85865775745, 89614952055⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231342080 231997440 265093120 267878400 ⟨⟨87354831438, 87354831445⟩, ⟨85491623348, 89231193046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 230686720 231342080 267878400 270663680 ⟨⟨88608698924, 88608698928⟩, ⟨86736921358, 90493684134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 231342080 231997440 267878400 270663680 ⟨⟨88226327065, 88226327072⟩, ⟨86359337405, 90106477033⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 231997440 232652800 265093120 267878400 ⟨⟨86976823832, 86976823837⟩, ⟨85118375074, 88848378883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 232652800 233308160 265093120 267878400 ⟨⟨86599734172, 86599734178⟩, ⟨84746024660, 88466503021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 231997440 232652800 267878400 270663680 ⟨⟨87844883889, 87844883896⟩, ⟨85982661928, 89720219086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 232652800 233308160 267878400 270663680 ⟨⟨87464362972, 87464362979⟩, ⟨85606888640, 89334903732⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 233308160 259522560 270663680 t = true :=
  ⟨_, (join_sr (m := 265093120) (by decide) (join_su (m := 231997440) (by decide) (join_sr (m := 262307840) (by decide) (join_su (m := 231342080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 231342080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 262307840) (by decide) (join_su (m := 232652800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 232652800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 231997440) (by decide) (join_sr (m := 267878400) (by decide) (join_su (m := 231342080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 231342080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 267878400) (by decide) (join_su (m := 232652800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 232652800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (89/320 : ℝ) →
    rho ∈ Set.Icc (99/320 : ℝ) (413/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e2 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  have e3 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

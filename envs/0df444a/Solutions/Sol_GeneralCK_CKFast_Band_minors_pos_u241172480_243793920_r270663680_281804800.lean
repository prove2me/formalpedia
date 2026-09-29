-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_243793920_r270663680_281804800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:19:18.346018+00:00
-- url     : https://prove2.me/submissions/4a64666f-48d5-4ed6-8ed8-8e89bf1e4b96

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 93/320]`, `ρ ∈ [413/1280, 43/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 241827840 270663680 273448960 ⟨⟨83418481430, 83418481437⟩, ⟨81617308719, 85232143870⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241827840 242483200 270663680 273448960 ⟨⟨83046858587, 83046858593⟩, ⟨81250175007, 84855988686⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241172480 241827840 273448960 276234240 ⟨⟨84237680581, 84237680587⟩, ⟨82432857490, 86055002109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 241827840 242483200 273448960 276234240 ⟨⟨83862699971, 83862699977⟩, ⟨82062374497, 85675480794⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 242483200 243138560 270663680 273448960 ⟨⟨82676071135, 82676071142⟩, ⟨80883858575, 84480687240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 243138560 243793920 270663680 273448960 ⟨⟨82306113346, 82306113353⟩, ⟨80518353814, 84106233682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 242483200 243138560 273448960 276234240 ⟨⟨83488558664, 83488558670⟩, ⟨81692712712, 85296817113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 243138560 243793920 273448960 276234240 ⟨⟨83115250918, 83115250924⟩, ⟨81323866507, 84919005200⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 241172480 241827840 276234240 279019520 ⟨⟨85056280124, 85056280131⟩, ⟨83247808579, 86877258761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 241827840 242483200 276234240 279019520 ⟨⟨84677949138, 84677949145⟩, ⟨82873983639, 86494378767⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 241172480 241827840 279019520 281804800 ⟨⟨85874282960, 85874282966⟩, ⟨84062164877, 87698916736⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 241827840 242483200 279019520 281804800 ⟨⟨85492608948, 85492608955⟩, ⟨83685005276, 87312685473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 242483200 243138560 276234240 279019520 ⟨⟨84300461299, 84300461307⟩, ⟨82500983761, 86112360232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243138560 243793920 276234240 279019520 ⟨⟨83923810847, 83923810853⟩, ⟨82128803305, 85731197276⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 242483200 243138560 279019520 281804800 ⟨⟨85111781855, 85111781862⟩, ⟨83308674525, 86927319424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 243138560 243793920 279019520 281804800 ⟨⟨84731795905, 84731795912⟩, ⟨82933166969, 86542812693⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 243793920 270663680 281804800 t = true :=
  ⟨_, (join_sr (m := 276234240) (by decide) (join_su (m := 242483200) (by decide) (join_sr (m := 273448960) (by decide) (join_su (m := 241827840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 241827840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 273448960) (by decide) (join_su (m := 243138560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 243138560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 242483200) (by decide) (join_sr (m := 279019520) (by decide) (join_su (m := 241827840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 241827840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 279019520) (by decide) (join_su (m := 243138560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 243138560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (413/1280 : ℝ) (43/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  have e3 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

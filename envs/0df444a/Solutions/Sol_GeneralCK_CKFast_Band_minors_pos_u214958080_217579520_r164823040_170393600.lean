-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_217579520_r164823040_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:40:19.455465+00:00
-- url     : https://prove2.me/submissions/a4440bd9-d017-4caa-8261-a64805e10057

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 83/320]`, `ρ ∈ [503/2560, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 214958080 215613440 164823040 166215680 ⟨⟨61662782257, 61662782263⟩, ⟨60114885970, 63220476193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 214958080 215613440 166215680 167608320 ⟨⟨62161818133, 62161818140⟩, ⟨60612005953, 63721432171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 215613440 216268800 164823040 166215680 ⟨⟨61396263337, 61396263342⟩, ⟨59851902715, 62950385200⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 215613440 216268800 166215680 167608320 ⟨⟨61893299012, 61893299019⟩, ⟨60347027324, 63449336203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 214958080 215613440 167608320 169000960 ⟨⟨62660558529, 62660558535⟩, ⟨61108831579, 64222091529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 214958080 215613440 169000960 170393600 ⟨⟨63159004232, 63159004239⟩, ⟨61605363632, 64722455057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 215613440 216268800 167608320 169000960 ⟨⟨62390042700, 62390042706⟩, ⟨60841861042, 63947994103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 215613440 216268800 169000960 170393600 ⟨⟨62886495176, 62886495182⟩, ⟨61336404645, 64446359679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 216268800 216924160 164823040 166215680 ⟨⟨61130591972, 61130591979⟩, ⟨59589748462, 62681160573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 216268800 216924160 166215680 167608320 ⟨⟨61625631967, 61625631974⟩, ⟨60082882211, 63178111124⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 216924160 217579520 164823040 166215680 ⟨⟨60865761644, 60865761650⟩, ⟨59328416836, 62412795641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 216924160 217579520 166215680 167608320 ⟨⟨61358810450, 61358810457⟩, ⟨59819564215, 62907750236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 216268800 216924160 167608320 169000960 ⟨⟨62120383431, 62120383438⟩, ⟨60575728503, 63674772054⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 216268800 216924160 169000960 170393600 ⟨⟨62614847129, 62614847136⟩, ⟨61068288101, 64171144129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 216924160 217579520 167608320 169000960 ⟨⟨61851574150, 61851574155⟩, ⟨60310427535, 63402418657⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 216924160 217579520 169000960 170393600 ⟨⟨62344053492, 62344053499⟩, ⟨60801007547, 63896801659⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 217579520 164823040 170393600 t = true :=
  ⟨_, (join_su (m := 216268800) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 215613440) (by decide) (join_sr (m := 166215680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 166215680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 215613440) (by decide) (join_sr (m := 169000960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 169000960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 167608320) (by decide) (join_su (m := 216924160) (by decide) (join_sr (m := 166215680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 166215680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 216924160) (by decide) (join_sr (m := 169000960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 169000960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (83/320 : ℝ) →
    rho ∈ Set.Icc (503/2560 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e2 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

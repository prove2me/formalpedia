-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_214958080_r270663680_281804800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:40:00.449762+00:00
-- url     : https://prove2.me/submissions/3f09ec75-234c-44d2-ace6-79c24163337e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 41/160]`, `ρ ∈ [413/1280, 43/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 211025920 270663680 273448960 ⟨⟨102152594833, 102152594841⟩, ⟨98721236495, 105625220629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 209715200 211025920 273448960 276234240 ⟨⟨103136094888, 103136094895⟩, ⟨99697296657, 106616179791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 211025920 212336640 270663680 273448960 ⟨⟨101316183731, 101316183737⟩, ⟨97900639261, 104772729029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 211025920 212336640 273448960 276234240 ⟨⟨102292565183, 102292565189⟩, ⟨98869605464, 105756546085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 209715200 211025920 276234240 279019520 ⟨⟨104118551787, 104118551794⟩, ⟨100672321987, 107606087187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209715200 211025920 279019520 281804800 ⟨⟨105099971304, 105099971312⟩, ⟨101646318207, 108594948642⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 211025920 212336640 276234240 279019520 ⟨⟨103267926265, 103267926273⟩, ⟨99837559296, 106739334494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 211025920 212336640 279019520 281804800 ⟨⟨104242272593, 104242272599⟩, ⟨100804506324, 107721099914⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 212336640 213647360 270663680 273448960 ⟨⟨100484393738, 100484393741⟩, ⟨97084511884, 103925012998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 212336640 213647360 273448960 276234240 ⟨⟨101453675078, 101453675080⟩, ⟨98046402874, 104901706155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 213647360 214958080 270663680 273448960 ⟨⟨99657159674, 99657159682⟩, ⟨96272791389, 103082005108⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 213647360 214958080 273448960 276234240 ⟨⟨100619359282, 100619359288⟩, ⟨97227625793, 104051592469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 212336640 213647360 276234240 279019520 ⟨⟨102421958431, 102421958434⟩, ⟨99007303560, 105877393370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 212336640 213647360 279019520 281804800 ⟨⟨103389249256, 103389249259⟩, ⟨99967219353, 106852080144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 213647360 214958080 276234240 279019520 ⟨⟨101580582888, 101580582894⟩, ⟨98181491568, 105020196190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 213647360 214958080 279019520 281804800 ⟨⟨102540835802, 102540835809⟩, ⟨99134393977, 105987821621⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 214958080 270663680 281804800 t = true :=
  ⟨_, (join_su (m := 212336640) (by decide) (join_sr (m := 276234240) (by decide) (join_su (m := 211025920) (by decide) (join_sr (m := 273448960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 273448960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 211025920) (by decide) (join_sr (m := 279019520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 279019520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 276234240) (by decide) (join_su (m := 213647360) (by decide) (join_sr (m := 273448960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 273448960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 213647360) (by decide) (join_sr (m := 279019520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 279019520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (413/1280 : ℝ) (43/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  have e3 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

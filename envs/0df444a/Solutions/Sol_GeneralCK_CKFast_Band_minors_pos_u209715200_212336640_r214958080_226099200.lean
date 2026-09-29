-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_212336640_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:05:27.186259+00:00
-- url     : https://prove2.me/submissions/bebb89fd-d36e-4066-afa4-f95d09cd3a7f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 81/320]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 210370560 214958080 217743360 ⟨⟨82427285797, 82427285804⟩, ⟨80468580229, 84400842499⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 210370560 211025920 214958080 217743360 ⟨⟨82081736495, 82081736503⟩, ⟨80128388502, 84049874239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 209715200 210370560 217743360 220528640 ⟨⟨83434813879, 83434813886⟩, ⟨81471953479, 85412527519⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 210370560 211025920 217743360 220528640 ⟨⟨83085452783, 83085452791⟩, ⟨81127959331, 85057738314⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 211025920 211681280 214958080 217743360 ⟨⟨81737238917, 81737238920⟩, ⟨79789222485, 83699984115⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 211681280 212336640 214958080 217743360 ⟨⟨81393785233, 81393785240⟩, ⟨79451074556, 83351164099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 211025920 211681280 217743360 220528640 ⟨⟨82737150328, 82737150329⟩, ⟨80784997828, 84704034139⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 211681280 212336640 217743360 220528640 ⟨⟨82389898646, 82389898654⟩, ⟨80443061317, 84351406929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 209715200 210370560 220528640 223313920 ⟨⟨84441170377, 84441170384⟩, ⟨82474161722, 86423034286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 210370560 211025920 220528640 223313920 ⟨⟨84088010735, 84088010741⟩, ⟨82126378279, 86064437505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 209715200 210370560 223313920 226099200 ⟨⟨85446361731, 85446361738⟩, ⟨83475211356, 87432369283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 210370560 211025920 223313920 226099200 ⟨⟨85089416693, 85089416700⟩, ⟨83123651652, 87069978197⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 211025920 211681280 220528640 223313920 ⟨⟨83735916520, 83735916523⟩, ⟨81779634293, 85706932517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 211681280 212336640 220528640 223313920 ⟨⟨83384879840, 83384879848⟩, ⟨81433922079, 85350511228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 211025920 211681280 223313920 226099200 ⟨⟨84733543748, 84733543752⟩, ⟨82773138094, 86708685541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 211681280 212336640 223313920 226099200 ⟨⟨84378734975, 84378734982⟩, ⟨82423662967, 86348483195⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 212336640 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 211025920) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 210370560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 210370560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 217743360) (by decide) (join_su (m := 211681280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 211681280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 211025920) (by decide) (join_sr (m := 223313920) (by decide) (join_su (m := 210370560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 210370560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 223313920) (by decide) (join_su (m := 211681280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 211681280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (81/320 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u170393600_173015040_r159252480_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:14:59.113954+00:00
-- url     : https://prove2.me/submissions/5a63b389-df55-4214-affc-007efc2d8b67

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/64, 33/160]`, `ρ ∈ [243/1280, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 170393600 171048960 159252480 162037760 ⟨⟨79930682751, 79930682759⟩, ⟨77690342631, 82190821178⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 171048960 171704320 159252480 162037760 ⟨⟨79595486712, 79595486720⟩, ⟨77362359875, 81848307044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 170393600 171048960 162037760 164823040 ⟨⟨81229076457, 81229076464⟩, ⟨78983729658, 83494204921⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 171048960 171704320 162037760 164823040 ⟨⟨80889080592, 80889080598⟩, ⟨78650958264, 83146880301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 171704320 172359680 159252480 162037760 ⟨⟨79261749428, 79261749431⟩, ⟨77035791116, 81507297306⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 172359680 173015040 159252480 162037760 ⟨⟨78929457979, 78929457986⟩, ⟨76710623877, 81167778600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 171704320 172359680 162037760 164823040 ⟨⟨80550557335, 80550557337⟩, ⟨78319614769, 82801073875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 172359680 173015040 162037760 164823040 ⟨⟨80213493686, 80213493693⟩, ⟨77989686612, 82456772201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 170393600 171048960 164823040 167608320 ⟨⟨82524895037, 82524895044⟩, ⟨80274561446, 84794993503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 171048960 171704320 164823040 167608320 ⟨⟨82180127397, 82180127405⟩, ⟨79937029179, 84442886738⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 170393600 171048960 167608320 170393600 ⟨⟨83818156352, 83818156360⟩, ⟨81562855679, 86093204962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 171048960 171704320 167608320 170393600 ⟨⟨83468644724, 83468644732⟩, ⟨81220590039, 85736344121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 171704320 172359680 164823040 167608320 ⟨⟨81836845935, 81836845939⟩, ⟨79600938431, 84092311675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 172359680 173015040 164823040 167608320 ⟨⟨81495037574, 81495037580⟩, ⟨79266276561, 83743254798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 171704320 172359680 167608320 170393600 ⟨⟨83120632559, 83120632563⟩, ⟨80879779260, 85381028206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 172359680 173015040 167608320 170393600 ⟨⟨82774106708, 82774106715⟩, ⟨80540410625, 85027243630⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 170393600 173015040 159252480 170393600 t = true :=
  ⟨_, (join_sr (m := 164823040) (by decide) (join_su (m := 171704320) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 171048960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 171048960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 162037760) (by decide) (join_su (m := 172359680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 172359680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 171704320) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 171048960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 171048960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 167608320) (by decide) (join_su (m := 172359680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 172359680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/64 : ℝ) (33/160 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e1 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

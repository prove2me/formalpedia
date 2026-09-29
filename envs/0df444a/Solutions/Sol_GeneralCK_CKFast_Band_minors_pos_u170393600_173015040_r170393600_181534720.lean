-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u170393600_173015040_r170393600_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:37:23.697753+00:00
-- url     : https://prove2.me/submissions/c426b76e-db4a-4167-aeee-ce92231fc36b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/64, 33/160]`, `ρ ∈ [13/64, 277/1280]` by 14 cells of the computing
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
theorem cell0 : cellOK 170393600 171048960 170393600 173178880 ⟨⟨85108878121, 85108878129⟩, ⟨82848629896, 87388857196⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 171048960 171704320 170393600 173178880 ⟨⟨84754650021, 84754650029⟩, ⟨82501658121, 87027270078⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 170393600 171048960 173178880 175964160 ⟨⟨86397077917, 86397077925⟩, ⟨84131901497, 88681967956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 171048960 171704320 173178880 175964160 ⟨⟨86038160603, 86038160610⟩, ⟨83780250566, 88315682094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 171704320 172359680 170393600 173178880 ⟨⟨84401934396, 84401934400⟩, ⟨82156154274, 86667240830⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 172359680 173015040 170393600 173178880 ⟨⟨84050718023, 84050718030⟩, ⟨81812105568, 86308755797⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 171704320 172359680 173178880 175964160 ⟨⟨85680768500, 85680768503⟩, ⟨83430080361, 87950966770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 172359680 173015040 173178880 175964160 ⟨⟨85324888317, 85324888324⟩, ⟨83081378024, 87587808264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 170393600 171048960 175964160 178749440 ⟨⟨87682773178, 87682773185⟩, ⟨85412687745, 89972554850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 171048960 171704320 175964160 178749440 ⟨⟨87319193644, 87319193650⟩, ⟨85056384381, 89601597515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 170393600 171704320 178749440 181534720 ⟨⟨88781679111, 88781679117⟩, ⟨85069666666, 92545622034⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 171704320 172359680 175964160 178749440 ⟨⟨86957151790, 86957151792⟩, ⟨84701574275, 89232223112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 172359680 173015040 175964160 178749440 ⟨⟨86596634259, 86596634265⟩, ⟨84348244502, 88864417861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 171704320 173015040 178749440 181534720 ⟨⟨88048345491, 88048345499⟩, ⟨84357272372, 91790874489⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 170393600 173015040 170393600 181534720 t = true :=
  ⟨_, (join_sr (m := 175964160) (by decide) (join_su (m := 171704320) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 171048960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 171048960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 173178880) (by decide) (join_su (m := 172359680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 172359680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 171704320) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 171048960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 178749440) (by decide) (join_su (m := 172359680) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/64 : ℝ) (33/160 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e1 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

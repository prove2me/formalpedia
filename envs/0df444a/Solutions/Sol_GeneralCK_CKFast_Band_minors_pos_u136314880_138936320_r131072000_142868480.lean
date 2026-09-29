-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_138936320_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:27:19.902946+00:00
-- url     : https://prove2.me/submissions/a6c68db9-f4df-4065-93fd-f93aba8311d9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 53/320]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 136970240 131072000 134021120 ⟨⟨83659245284, 83659245291⟩, ⟨80965158275, 86382016317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136970240 137625600 131072000 134021120 ⟨⟨83285561386, 83285561394⟩, ⟨80602035255, 85997578815⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 136314880 136970240 134021120 136970240 ⟨⟨85371280001, 85371280009⟩, ⟨82670867839, 88100308754⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 136970240 137625600 134021120 136970240 ⟨⟨84991073843, 84991073851⟩, ⟨82301233944, 87709339055⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 137625600 138280960 131072000 134021120 ⟨⟨82914063927, 82914063934⟩, ⟨80241016205, 85615412265⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 138280960 138936320 131072000 134021120 ⟨⟨82544729353, 82544729362⟩, ⟨79882078576, 85235492085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 137625600 138280960 134021120 136970240 ⟨⟨84613079720, 84613079727⟩, ⟨81933729796, 87320665697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 138280960 138936320 134021120 136970240 ⟨⟨84237273903, 84237273912⟩, ⟨81568332664, 86934263935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 136314880 136970240 136970240 139919360 ⟨⟨87077776684, 87077776691⟩, ⟨84371092446, 89813009918⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 136970240 137625600 136970240 139919360 ⟨⟨86691109811, 86691109818⟩, ⟨83995008493, 89415570292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 136314880 136970240 139919360 142868480 ⟨⟨88778787865, 88778787872⟩, ⟨86065883896, 91520173080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 136970240 137625600 139919360 142868480 ⟨⟨88385720977, 88385720984⟩, ⟨85683409875, 91116324937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 137625600 138280960 136970240 139919360 ⟨⟨86306679867, 86306679874⟩, ⟨83621079372, 89020451688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 138280960 138936320 136970240 139919360 ⟨⟨85924462965, 85924462972⟩, ⟨83249282182, 88627629203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 137625600 138280960 139919360 142868480 ⟨⟨87994915229, 87994915236⟩, ⟨85303115093, 90714821803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 138280960 138936320 139919360 142868480 ⟨⟨87606346581, 87606346588⟩, ⟨84924976489, 90315638631⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 138936320 131072000 142868480 t = true :=
  ⟨_, (join_sr (m := 136970240) (by decide) (join_su (m := 137625600) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 136970240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 136970240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 134021120) (by decide) (join_su (m := 138280960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 138280960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 137625600) (by decide) (join_sr (m := 139919360) (by decide) (join_su (m := 136970240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 136970240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 139919360) (by decide) (join_su (m := 138280960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 138280960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (53/320 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((138936320 : ℤ) : ℝ) / (D : ℝ)) = (53/320 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

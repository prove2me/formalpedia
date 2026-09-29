-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_222822400_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:18:40.751026+00:00
-- url     : https://prove2.me/submissions/faaf98ea-e582-4009-aa64-ff28a3c4b4ca

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 17/64]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 220856320 214958080 217743360 ⟨⟨77020443437, 77020443443⟩, ⟨75144447377, 78910354937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220856320 221511680 214958080 217743360 ⟨⟨76690819769, 76690819772⟩, ⟨74819788279, 78575711355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 220200960 220856320 217743360 220528640 ⟨⟨77967794640, 77967794647⟩, ⟨76087795847, 79861714172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 220856320 221511680 217743360 220528640 ⟨⟨77634465979, 77634465981⟩, ⟨75759441386, 79523356141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 221511680 222167040 214958080 217743360 ⟨⟨76362130430, 76362130437⟩, ⟨74496040508, 78242025460⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 222167040 222822400 214958080 217743360 ⟨⟨76034368607, 76034368612⟩, ⟨74173197416, 77909290260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 221511680 222167040 217743360 220528640 ⟨⟨77302078051, 77302078058⟩, ⟨75432004667, 79185962189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222167040 222822400 217743360 220528640 ⟨⟨76970624015, 76970624022⟩, ⟨75105479014, 78849525294⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 220200960 220856320 220528640 223313920 ⟨⟨78914171776, 78914171782⟩, ⟨77030175070, 80812094439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 220856320 221511680 220528640 223313920 ⟨⟨78577149489, 78577149492⟩, ⟨76698136515, 80470033429⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 220200960 220856320 223313920 226099200 ⟨⟨79859579923, 79859579931⟩, ⟨77971590099, 81761500850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 220856320 221511680 223313920 226099200 ⟨⟨79518875307, 79518875310⟩, ⟨77635878644, 81415748254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 221511680 222167040 220528640 223313920 ⟨⟨78241074234, 78241074241⟩, ⟨76367022012, 80128942781⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 222167040 222822400 220528640 223313920 ⟨⟨77905939138, 77905939144⟩, ⟨76036824852, 79788815443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 221511680 222167040 223313920 226099200 ⟨⟨79179123911, 79179123918⟩, ⟨77301097445, 81070972194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 222167040 222822400 223313920 226099200 ⟨⟨78840318834, 78840318841⟩, ⟨76967239763, 80727165590⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 222822400 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 221511680) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 220856320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 220856320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 217743360) (by decide) (join_su (m := 222167040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 222167040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 221511680) (by decide) (join_sr (m := 223313920) (by decide) (join_su (m := 220856320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 220856320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 223313920) (by decide) (join_su (m := 222167040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 222167040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (17/64 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

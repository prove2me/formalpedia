-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_209715200_r393216000_415498240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:51:36.077986+00:00
-- url     : https://prove2.me/submissions/340cd14e-9e6d-4221-92b2-1bf1d89d886b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 1/4]`, `ρ ∈ [15/32, 317/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 204472320 205783040 393216000 398786560 ⟨⟨149569166825, 149569166832⟩, ⟨145066828968, 154132122671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 205783040 207093760 393216000 398786560 ⟨⟨148414896253, 148414896258⟩, ⟨143936124678, 152953909439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 204472320 205783040 398786560 404357120 ⟨⟨151502940698, 151502940706⟩, ⟨146985288621, 156081165698⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205783040 207093760 398786560 404357120 ⟨⟨150336166895, 150336166900⟩, ⟨145842103693, 154890431207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 207093760 208404480 393216000 398786560 ⟨⟨147266001539, 147266001546⟩, ⟨142810608875, 151781262762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 208404480 209715200 393216000 398786560 ⟨⟨146122413440, 146122413448⟩, ⟨141690214699, 150614110980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 207093760 208404480 398786560 404357120 ⟨⟨149174775970, 149174775977⟩, ⟨144704115613, 153705268853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 208404480 209715200 398786560 404357120 ⟨⟨148018698882, 148018698889⟩, ⟨143571257683, 152525607209⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 205783040 404357120 409927680 ⟨⟨153433214972, 153433214979⟩, ⟨148900287181, 158026669212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 205783040 207093760 404357120 409927680 ⟨⟨152254008160, 152254008162⟩, ⟨147744690634, 156823484902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 204472320 205783040 409927680 415498240 ⟨⟨155360030972, 155360030981⟩, ⟨150811865452, 159968675069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 205783040 207093760 409927680 415498240 ⟨⟨154168460348, 154168460353⟩, ⟨149643925293, 158753111341⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 207093760 208404480 404357120 409927680 ⟨⟨151080190188, 151080190194⟩, ⟨146594298252, 155625877238⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 208404480 209715200 404357120 409927680 ⟨⟨149911692229, 149911692236⟩, ⟨145449043515, 154433775041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 207093760 208404480 409927680 415498240 ⟨⟨152982283493, 152982283501⟩, ⟨148481195599, 157543127715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 208404480 209715200 409927680 415498240 ⟨⟨151801431802, 151801431810⟩, ⟨147323610041, 156338653273⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 209715200 393216000 415498240 t = true :=
  ⟨_, (join_sr (m := 404357120) (by decide) (join_su (m := 207093760) (by decide) (join_sr (m := 398786560) (by decide) (join_su (m := 205783040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 205783040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 398786560) (by decide) (join_su (m := 208404480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 208404480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 207093760) (by decide) (join_sr (m := 409927680) (by decide) (join_su (m := 205783040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 205783040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 409927680) (by decide) (join_su (m := 208404480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 208404480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (15/32 : ℝ) (317/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  have e3 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

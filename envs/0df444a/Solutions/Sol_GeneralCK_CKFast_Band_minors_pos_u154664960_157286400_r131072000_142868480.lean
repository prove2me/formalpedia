-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u154664960_157286400_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:39:12.736164+00:00
-- url     : https://prove2.me/submissions/109d86d5-f29b-48bb-8f54-aeef81b2eefb

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [59/320, 3/16]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 154664960 155320320 131072000 134021120 ⟨⟨73951755657, 73951755665⟩, ⟨71525173990, 76402312111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 155320320 155975680 131072000 134021120 ⟨⟨73631379612, 73631379616⟩, ⟨71213380705, 76073208282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 154664960 155320320 134021120 136970240 ⟨⟨75490298851, 75490298859⟩, ⟨73057762066, 77946775159⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 155320320 155975680 134021120 136970240 ⟨⟨75164055437, 75164055441⟩, ⟨72740116020, 77611790234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 155975680 156631040 131072000 134021120 ⟨⟨73312640268, 73312640276⟩, ⟨70903164477, 75745802196⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 156631040 157286400 131072000 134021120 ⟨⟨72995521575, 72995521583⟩, ⟨70594509901, 75420077126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 155975680 156631040 134021120 136970240 ⟨⟨74839469880, 74839469886⟩, ⟨72424068247, 77278524127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 156631040 157286400 134021120 136970240 ⟨⟨74516525980, 74516525988⟩, ⟨72109603194, 76946959974⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 154664960 155320320 136970240 139919360 ⟨⟨77024789941, 77024789948⟩, ⟨74586333825, 79487150112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 155320320 155975680 136970240 139919360 ⟨⟨76692724133, 76692724135⟩, ⟨74262879482, 79146329577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 154664960 155320320 139919360 142868480 ⟨⟨78555262495, 78555262502⟩, ⟨76110922432, 81023470954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 155320320 155975680 139919360 142868480 ⟨⟨78217418740, 78217418743⟩, ⟨75781703736, 80676859756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 155975680 156631040 136970240 139919360 ⟨⟨76362336842, 76362336849⟩, ⟨73941044143, 78807248439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 156631040 157286400 136970240 139919360 ⟨⟨76033611736, 76033611743⟩, ⟨73620812111, 78469889700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 155975680 156631040 139919360 142868480 ⟨⟨77881273681, 77881273689⟩, ⟨75454124297, 80332008049⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 156631040 157286400 139919360 142868480 ⟨⟨77546810856, 77546810864⟩, ⟨75128168285, 79988898700⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 154664960 157286400 131072000 142868480 t = true :=
  ⟨_, (join_sr (m := 136970240) (by decide) (join_su (m := 155975680) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 155320320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 155320320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 134021120) (by decide) (join_su (m := 156631040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 156631040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 155975680) (by decide) (join_sr (m := 139919360) (by decide) (join_su (m := 155320320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 155320320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 139919360) (by decide) (join_su (m := 156631040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 156631040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (59/320 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

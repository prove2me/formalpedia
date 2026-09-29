-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_209715200_r348651520_370933760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:45:00.978993+00:00
-- url     : https://prove2.me/submissions/d610c5f8-973e-4b6f-b58c-249f27f7f159

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 1/4]`, `ρ ∈ [133/320, 283/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 204472320 205783040 348651520 354222080 ⟨⟨133967904173, 133967904180⟩, ⟨129589531992, 138407204028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 205783040 207093760 348651520 354222080 ⟨⟨132916315141, 132916315143⟩, ⟨128561282649, 137331862904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 204472320 205783040 354222080 359792640 ⟨⟨135931208973, 135931208979⟩, ⟨131537194699, 140386117178⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205783040 207093760 354222080 359792640 ⟨⟨134866516316, 134866516321⟩, ⟨130495874706, 139297643906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 207093760 208404480 348651520 354222080 ⟨⟨131870004910, 131870004917⟩, ⟨127538114706, 136262002153⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 208404480 209715200 348651520 354222080 ⟨⟨130828903099, 130828903106⟩, ⟨126519960435, 135197548667⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 207093760 208404480 354222080 359792640 ⟨⟨133807118800, 133807118809⟩, ⟨129459653634, 138214666056⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 208404480 209715200 354222080 359792640 ⟨⟨132752946134, 132752946141⟩, ⟨128428463814, 137137110651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 205783040 359792640 365363200 ⟨⟨137890669527, 137890669535⟩, ⟨133481056129, 142361141692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 205783040 207093760 359792640 365363200 ⟨⟨136812952189, 136812952194⟩, ⟨132426743056, 141259616603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 204472320 205783040 365363200 370933760 ⟨⟨139846330338, 139846330346⟩, ⟨135421160199, 144332322655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 205783040 207093760 365363200 370933760 ⟨⟨138755666118, 138755666123⟩, ⟨134353930496, 143217824910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 207093760 208404480 359792640 365363200 ⟨⟨135740545077, 135740545086⟩, ⟨131377545194, 140163600708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 208404480 209715200 359792640 365363200 ⟨⟨134673378008, 134673378016⟩, ⟨130333394948, 139073021178⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 207093760 208404480 365363200 370933760 ⟨⟨137670325982, 137670325990⟩, ⟨133291831089, 142108848889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 208404480 209715200 365363200 370933760 ⟨⟨136590239868, 136590239876⟩, ⟨132234794469, 141005321918⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 209715200 348651520 370933760 t = true :=
  ⟨_, (join_sr (m := 359792640) (by decide) (join_su (m := 207093760) (by decide) (join_sr (m := 354222080) (by decide) (join_su (m := 205783040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 205783040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 354222080) (by decide) (join_su (m := 208404480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 208404480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 207093760) (by decide) (join_sr (m := 365363200) (by decide) (join_su (m := 205783040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 205783040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 365363200) (by decide) (join_su (m := 208404480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 208404480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (133/320 : ℝ) (283/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  have e3 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_237240320_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:41:39.573467+00:00
-- url     : https://prove2.me/submissions/7cde1a31-d280-45d1-829a-96f44fcb2629

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 181/640]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 236257280 142540800 143933440 ⟨⟨46555500310, 46555500316⟩, ⟨45721984768, 47392125211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 236257280 236584960 142540800 143933440 ⟨⟨46449287724, 46449287729⟩, ⟨45616820803, 47284857653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 235929600 236257280 143933440 145326080 ⟨⟨46996381519, 46996381525⟩, ⟨46161902637, 47833971057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 236257280 236584960 143933440 145326080 ⟨⟨46889213145, 46889213151⟩, ⟨46055784371, 47725746232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 236584960 236912640 142540800 143933440 ⟨⟨46343226416, 46343226419⟩, ⟨45511805727, 47177743785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 236912640 237240320 142540800 143933440 ⟨⟨46237315813, 46237315818⟩, ⟨45406938969, 47070783030⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 236584960 236912640 143933440 145326080 ⟨⟨46782197097, 46782197100⟩, ⟨45949816038, 47617676144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 236912640 237240320 143933440 145326080 ⟨⟨46675332795, 46675332800⟩, ⟨45843997065, 47509760213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 236257280 145326080 146718720 ⟨⟨47437054669, 47437054674⟩, ⟨46601612846, 48275608440⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 236257280 236584960 145326080 146718720 ⟨⟨47328931836, 47328931841⟩, ⟨46494541603, 48166427681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 235929600 236257280 146718720 148111360 ⟨⟨47877520255, 47877520260⟩, ⟨47041115892, 48717037857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 236257280 236584960 146718720 148111360 ⟨⟨47768444287, 47768444293⟩, ⟨46933092989, 48606902496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 236584960 236912640 145326080 146718720 ⟨⟨47220962368, 47220962370⟩, ⟨46387621329, 48057402701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 236912640 237240320 145326080 146718720 ⟨⟨47113145681, 47113145686⟩, ⟨46280851449, 47948532914⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 236584960 236912640 146718720 148111360 ⟨⟨47659522716, 47659522719⟩, ⟨46825222086, 48496923943⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 236912640 237240320 146718720 148111360 ⟨⟨47550754953, 47550754960⟩, ⟨46717502603, 48387101616⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 237240320 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 236584960) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 236257280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 236257280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 236912640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 236912640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 236584960) (by decide) (join_sr (m := 146718720) (by decide) (join_su (m := 236257280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 236257280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 146718720) (by decide) (join_su (m := 236912640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 236912640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (181/640 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

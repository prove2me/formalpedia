-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u131072000_136314880_r272629760_296222720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:43:43.956801+00:00
-- url     : https://prove2.me/submissions/c58c37f2-e7b9-4195-97be-847c6464e954

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [5/32, 13/80]`, `ρ ∈ [13/40, 113/320]` by 15 cells of the computing
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
theorem cell0 : cellOK 131072000 132382720 272629760 278528000 ⟨⟨165970503272, 165970503280⟩, ⟨159933433079, 172112742355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 132382720 133693440 272629760 278528000 ⟨⟨164665906969, 164665906977⟩, ⟨158672496760, 170763409570⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 131072000 132382720 278528000 284426240 ⟨⟨169020364801, 169020364811⟩, ⟨162965894658, 175179359920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 132382720 133693440 278528000 284426240 ⟨⟨167698508991, 167698508999⟩, ⟨161687592086, 173812896019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 133693440 135004160 272629760 278528000 ⟨⟨163373297732, 163373297739⟩, ⟨157422975757, 169426652482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 135004160 136314880 272629760 278528000 ⟨⟨162092460020, 162092460030⟩, ⟨156184665994, 168102243739⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 133693440 135004160 278528000 284426240 ⟨⟨166388666496, 166388666502⟩, ⟨160420737745, 172459026781⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 135004160 136314880 278528000 284426240 ⟨⟨165090622881, 165090622891⟩, ⟨159165128432, 171117526219⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 131072000 132382720 284426240 290324480 ⟨⟨172055064957, 172055064968⟩, ⟨165983431868, 178230579752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 132382720 133693440 284426240 290324480 ⟨⟨170716223322, 170716223332⟩, ⟨164688032482, 176847262455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 131072000 133693440 290324480 296222720 ⟨⟨174395571022, 174395571032⟩, ⟨164692959300, 184363515411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 133693440 135004160 284426240 290324480 ⟨⟨169389416942, 169389416946⟩, ⟨163404109952, 175476554472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 135004160 136314880 284426240 290324480 ⟨⟨168074432548, 168074432558⟩, ⟨162131462012, 174118231234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 133693440 135004160 290324480 296222720 ⟨⟨172375803183, 172375803186⟩, ⟨166373340725, 178479495475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 135004160 136314880 290324480 296222720 ⟨⟨171044136602, 171044136612⟩, ⟨165083908728, 177104611994⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 131072000 136314880 272629760 296222720 t = true :=
  ⟨_, (join_sr (m := 284426240) (by decide) (join_su (m := 133693440) (by decide) (join_sr (m := 278528000) (by decide) (join_su (m := 132382720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 132382720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 278528000) (by decide) (join_su (m := 135004160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 135004160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 133693440) (by decide) (join_sr (m := 290324480) (by decide) (join_su (m := 132382720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 290324480) (by decide) (join_su (m := 135004160) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 135004160) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (5/32 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (13/40 : ℝ) (113/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  have e3 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

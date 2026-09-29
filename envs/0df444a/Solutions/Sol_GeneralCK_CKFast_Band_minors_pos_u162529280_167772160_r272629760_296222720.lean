-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_167772160_r272629760_296222720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:01:49.130753+00:00
-- url     : https://prove2.me/submissions/75d75a8a-0f2b-44f8-82dc-7ce73356f666

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 1/5]`, `ρ ∈ [13/40, 113/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 162529280 163840000 272629760 278528000 ⟨⟨137580931091, 137580931100⟩, ⟨132454242437, 142790984642⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 163840000 165150720 272629760 278528000 ⟨⟨136513467877, 136513467885⟩, ⟨131419357492, 141690190312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 162529280 163840000 278528000 284426240 ⟨⟨140225488358, 140225488367⟩, ⟨135080281910, 145453798328⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163840000 165150720 278528000 284426240 ⟨⟨139141599332, 139141599341⟩, ⟨134028974020, 144336586385⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 165150720 166461440 272629760 278528000 ⟨⟨135453968915, 135453968922⟩, ⟨130392073090, 140597734397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 166461440 167772160 272629760 278528000 ⟨⟨134402307872, 134402307876⟩, ⟨129372269196, 139513484061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 165150720 166461440 278528000 284426240 ⟨⟨138065714591, 138065714598⟩, ⟨132985309558, 143227749738⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 166461440 167772160 278528000 284426240 ⟨⟨136997707967, 136997707971⟩, ⟨131949168561, 142127155826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 162529280 163840000 284426240 290324480 ⟨⟨142860377364, 142860377371⟩, ⟨137696797367, 148106797665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 163840000 165150720 284426240 290324480 ⟨⟨141760248029, 141760248038⟩, ⟨136629248694, 146973356926⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 162529280 163840000 290324480 296222720 ⟨⟨145485740970, 145485740977⟩, ⟨140303928888, 150750128335⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 163840000 165150720 290324480 296222720 ⟨⟨144369553111, 144369553119⟩, ⟨139220317967, 149600643802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 165150720 166461440 284426240 290324480 ⟨⟨140668159970, 140668159979⟩, ⟨135569383339, 145848325281⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 166461440 167772160 284426240 290324480 ⟨⟨139583987235, 139583987239⟩, ⟨134517081453, 144731570489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 165150720 166461440 290324480 296222720 ⟨⟨143261440571, 143261440580⟩, ⟨138144427350, 148459599171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 166461440 167772160 290324480 296222720 ⟨⟨142161277656, 142161277659⟩, ⟨137076137348, 147326862570⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 167772160 272629760 296222720 t = true :=
  ⟨_, (join_sr (m := 284426240) (by decide) (join_su (m := 165150720) (by decide) (join_sr (m := 278528000) (by decide) (join_su (m := 163840000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 163840000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 278528000) (by decide) (join_su (m := 166461440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 166461440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 165150720) (by decide) (join_sr (m := 290324480) (by decide) (join_su (m := 163840000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 163840000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 290324480) (by decide) (join_su (m := 166461440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 166461440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (13/40 : ℝ) (113/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  have e3 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

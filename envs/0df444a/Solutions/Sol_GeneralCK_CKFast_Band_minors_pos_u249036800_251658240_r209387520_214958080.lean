-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_251658240_r209387520_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:32:15.986586+00:00
-- url     : https://prove2.me/submissions/f707733f-84f6-4ba7-a405-f9d1f752a836

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 3/10]`, `ρ ∈ [639/2560, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249692160 209387520 210780160 ⟨⟨61538097314, 61538097319⟩, ⟨60098885906, 62985693417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249036800 249692160 210780160 212172800 ⟨⟨61933804583, 61933804588⟩, ⟨60492926139, 63383073472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249692160 250347520 209387520 210780160 ⟨⟨61251601206, 61251601212⟩, ⟨59815263590, 62696298481⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249692160 250347520 210780160 212172800 ⟨⟨61645573409, 61645573416⟩, ⟨60207572871, 63091939384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249036800 249692160 212172800 213565440 ⟨⟨62329368686, 62329368691⟩, ⟨60886823376, 63780310185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 249036800 249692160 213565440 214958080 ⟨⟨62724789950, 62724789955⟩, ⟨61280577943, 64177403881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249692160 250347520 212172800 213565440 ⟨⟨62039404315, 62039404320⟩, ⟨60599741012, 63487438825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 249692160 250347520 213565440 214958080 ⟨⟨62433094244, 62433094250⟩, ⟨60991768334, 63882797121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 250347520 251002880 209387520 210780160 ⟨⟨60965773911, 60965773914⟩, ⟨59532297329, 62407585262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 250347520 251002880 210780160 212172800 ⟨⟨61358013700, 61358013703⟩, ⟨59922878304, 62801489666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 251002880 251658240 209387520 210780160 ⟨⟨60680610657, 60680610664⟩, ⟨59249982438, 62119548908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 251002880 251658240 210780160 212172800 ⟨⟨61071120667, 61071120674⟩, ⟨59638837744, 62511719450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 250347520 251002880 212172800 213565440 ⟨⟨61750114039, 61750114042⟩, ⟨60313319979, 63195254466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250347520 251002880 213565440 214958080 ⟨⟨62142075246, 62142075249⟩, ⟨60703622667, 63588879980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 251002880 251658240 212172800 213565440 ⟨⟨61461493059, 61461493064⟩, ⟨60027555568, 62903752230⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251002880 251658240 213565440 214958080 ⟨⟨61851728143, 61851728148⟩, ⟨60416136219, 63295647558⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 251658240 209387520 214958080 t = true :=
  ⟨_, (join_su (m := 250347520) (by decide) (join_sr (m := 212172800) (by decide) (join_su (m := 249692160) (by decide) (join_sr (m := 210780160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 210780160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 249692160) (by decide) (join_sr (m := 213565440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 213565440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 212172800) (by decide) (join_su (m := 251002880) (by decide) (join_sr (m := 210780160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 210780160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 251002880) (by decide) (join_sr (m := 213565440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 213565440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (639/2560 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((209387520 : ℤ) : ℝ) / (D : ℝ)) = (639/2560 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_249036800_r209387520_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:27:24.465708+00:00
-- url     : https://prove2.me/submissions/71579c9c-8032-44b0-88d2-5409187fb35d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 19/64]`, `ρ ∈ [639/2560, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247070720 209387520 210780160 ⟨⟨62690866431, 62690866438⟩, ⟨61240030525, 64150188683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246415360 247070720 210780160 212172800 ⟨⟨63093540764, 63093540770⟩, ⟨61641021351, 64554552166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247070720 247726080 209387520 210780160 ⟨⟨62401646703, 62401646707⟩, ⟨60953736496, 63858017613⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247070720 247726080 210780160 212172800 ⟨⟨62802575220, 62802575224⟩, ⟨61352985627, 64260631186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 246415360 247070720 212172800 213565440 ⟨⟨63496064263, 63496064270⟩, ⟨62041861563, 64958764588⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246415360 247070720 213565440 214958080 ⟨⟨63898437278, 63898437283⟩, ⟨62442551505, 65362826301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247070720 247726080 212172800 213565440 ⟨⟨63203354850, 63203354854⟩, ⟨61752086078, 64663095660⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247070720 247726080 213565440 214958080 ⟨⟨63603985936, 63603985940⟩, ⟨62151038188, 65065411376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 247726080 248381440 209387520 210780160 ⟨⟨62113115206, 62113115211⟩, ⟨60668117591, 63566548038⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 247726080 248381440 210780160 212172800 ⟨⟨62512300617, 62512300623⟩, ⟨61065627735, 63967414415⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 248381440 249036800 209387520 210780160 ⟨⟨61825267035, 61825267040⟩, ⟨60383168989, 63275774961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 248381440 249036800 210780160 212172800 ⟨⟨62222712034, 62222712041⟩, ⟨60778942839, 63674896837⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 247726080 248381440 212172800 213565440 ⟨⟨62911339068, 62911339074⟩, ⟨61462991113, 64368133629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 247726080 248381440 213565440 214958080 ⟨⟨63310230895, 63310230901⟩, ⟨61860208059, 64768706020⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 248381440 249036800 212172800 213565440 ⟨⟨62620011982, 62620011987⟩, ⟨61174571818, 64073873469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 248381440 249036800 213565440 214958080 ⟨⟨63017167206, 63017167212⟩, ⟨61570056254, 64472705190⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 249036800 209387520 214958080 t = true :=
  ⟨_, (join_su (m := 247726080) (by decide) (join_sr (m := 212172800) (by decide) (join_su (m := 247070720) (by decide) (join_sr (m := 210780160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 210780160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 247070720) (by decide) (join_sr (m := 213565440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 213565440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 212172800) (by decide) (join_su (m := 248381440) (by decide) (join_sr (m := 210780160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 210780160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 248381440) (by decide) (join_sr (m := 213565440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 213565440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (639/2560 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((209387520 : ℤ) : ℝ) / (D : ℝ)) = (639/2560 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

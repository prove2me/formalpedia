-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_222822400_r248381440_259522560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:35:01.111302+00:00
-- url     : https://prove2.me/submissions/86467913-57b6-464a-b584-558b7e4801b3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 17/64]`, `ρ ∈ [379/1280, 99/320]` by 11 cells of the computing
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
theorem cell0 : cellOK 220200960 220856320 248381440 251166720 ⟨⟨88325475597, 88325475605⟩, ⟨86401758718, 90263166367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220856320 221511680 248381440 251166720 ⟨⟨87952126081, 87952126084⟩, ⟨86033482920, 89884689947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 220200960 221511680 251166720 253952000 ⟨⟨89072880090, 89072880097⟩, ⟨85814738800, 92370043140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 221511680 222167040 248381440 251166720 ⟨⟨87579780805, 87579780813⟩, ⟨85666188566, 89507240887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 222167040 222822400 248381440 251166720 ⟨⟨87208432641, 87208432648⟩, ⟨85299868686, 89130811889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 221511680 222167040 251166720 253952000 ⟨⟨88508631723, 88508631731⟩, ⟨86591109738, 90440026287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222167040 222822400 251166720 253952000 ⟨⟨88133720454, 88133720460⟩, ⟨86221235281, 90060025834⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 220200960 221511680 253952000 256737280 ⟨⟨90006175951, 90006175958⟩, ⟨86740756261, 93310646668⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 220200960 221511680 256737280 259522560 ⟨⟨90938567212, 90938567220⟩, ⟨87665875272, 94250339205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 221511680 222822400 253952000 256737280 ⟨⟨89247231410, 89247231416⟩, ⟨85996310361, 92536955723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 221511680 222822400 256737280 259522560 ⟨⟨90172527635, 90172527643⟩, ⟨86914362457, 93469525995⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 222822400 248381440 259522560 t = true :=
  ⟨_, (join_sr (m := 253952000) (by decide) (join_su (m := 221511680) (by decide) (join_sr (m := 251166720) (by decide) (join_su (m := 220856320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 251166720) (by decide) (join_su (m := 222167040) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (join_su (m := 222167040) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_su (m := 221511680) (by decide) (join_sr (m := 256737280) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 256737280) (by decide) (leaf_ok cell9) (leaf_ok cell10))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (17/64 : ℝ) →
    rho ∈ Set.Icc (379/1280 : ℝ) (99/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e2 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  have e3 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

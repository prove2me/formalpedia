-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_246415360_r209387520_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:23:14.926703+00:00
-- url     : https://prove2.me/submissions/c860c038-8bd0-41c4-a0b0-07fa91400d7b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 47/160]`, `ρ ∈ [639/2560, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 243793920 244449280 209387520 210780160 ⟨⟨63854727181, 63854727184⟩, ⟨62392055556, 65325989265⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 243793920 244449280 210780160 212172800 ⟨⟨64264412166, 64264412169⟩, ⟨62800040539, 65737379783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 244449280 245104640 209387520 210780160 ⟨⟨63562704676, 63562704682⟩, ⟨62103012102, 65030961447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244449280 245104640 210780160 212172800 ⟨⟨63970632859, 63970632866⟩, ⟨62509244409, 65440591066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243793920 244449280 212172800 213565440 ⟨⟨64673938331, 64673938334⟩, ⟨63207866968, 66148611205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 243793920 244449280 213565440 214958080 ⟨⟨65083306048, 65083306051⟩, ⟨63615535215, 66559683900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 244449280 245104640 212172800 213565440 ⟨⟨64378404250, 64378404256⟩, ⟨62915320179, 65850063629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 244449280 245104640 213565440 214958080 ⟨⟨64786019213, 64786019219⟩, ⟨63321239773, 66259379500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 245104640 245760000 209387520 210780160 ⟨⟨63271390417, 63271390422⟩, ⟨61814663418, 64736655506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 245104640 245760000 210780160 212172800 ⟨⟨63677564568, 63677564573⟩, ⟨62219145817, 65144526997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245760000 246415360 209387520 210780160 ⟨⟨62980779343, 62980779348⟩, ⟨61527004534, 64443066290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245760000 246415360 210780160 212172800 ⟨⟨63385202214, 63385202220⟩, ⟨61929739779, 64849182405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 245104640 245760000 212172800 213565440 ⟨⟨64083583932, 64083583938⟩, ⟨62623473673, 65552243450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245104640 245760000 213565440 214958080 ⟨⟨64489448870, 64489448875⟩, ⟨63027647343, 65959805225⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245760000 246415360 212172800 213565440 ⟨⟨63789472287, 63789472293⟩, ⟨62332322453, 65255145484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245760000 246415360 213565440 214958080 ⟨⟨64193589913, 64193589919⟩, ⟨62734752911, 65660955877⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 246415360 209387520 214958080 t = true :=
  ⟨_, (join_su (m := 245104640) (by decide) (join_sr (m := 212172800) (by decide) (join_su (m := 244449280) (by decide) (join_sr (m := 210780160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 210780160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 244449280) (by decide) (join_sr (m := 213565440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 213565440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 212172800) (by decide) (join_su (m := 245760000) (by decide) (join_sr (m := 210780160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 210780160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 245760000) (by decide) (join_sr (m := 213565440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 213565440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (639/2560 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((209387520 : ℤ) : ℝ) / (D : ℝ)) = (639/2560 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

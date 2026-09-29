-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_238551040_r181534720_187105280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:44:57.030439+00:00
-- url     : https://prove2.me/submissions/816de8da-cd39-4088-b60c-1ae340ced128

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 91/320]`, `ρ ∈ [277/1280, 571/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 236584960 181534720 182927360 ⟨⟨58756866999, 58756867004⟩, ⟨57292446353, 60230100938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 235929600 236584960 182927360 184320000 ⟨⟨59191646568, 59191646574⟩, ⟨57725467359, 60666644434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 236584960 237240320 181534720 182927360 ⟨⟨58492251898, 58492251903⟩, ⟨57030893568, 59962394586⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 236584960 237240320 182927360 184320000 ⟨⟨58925193039, 58925193046⟩, ⟨57462080591, 60397095242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235929600 236584960 184320000 185712640 ⟨⟨59626232193, 59626232198⟩, ⟨58158294877, 61102993517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235929600 236584960 185712640 187105280 ⟨⟨60060624339, 60060624344⟩, ⟨58590929375, 61539148652⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 236584960 237240320 184320000 185712640 ⟨⟨59357942665, 59357942672⟩, ⟨57893076541, 60831603927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 236584960 237240320 185712640 187105280 ⟨⟨59790501234, 59790501239⟩, ⟨58323881875, 61265921103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 237240320 237895680 181534720 182927360 ⟨⟨58228344899, 58228344902⟩, ⟨56770034278, 59695411124⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 237240320 237895680 182927360 184320000 ⟨⟨58659451040, 58659451043⟩, ⟨57199390743, 60128272369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 237895680 238551040 181534720 182927360 ⟨⟨57965140805, 57965140811⟩, ⟨56509863396, 59429145252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 237895680 238551040 182927360 184320000 ⟨⟨58394415353, 58394415358⟩, ⟨56937392703, 59860170497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 237240320 237895680 184320000 185712640 ⟨⟨59090368070, 59090368072⟩, ⟨57628558521, 60560944063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 237240320 237895680 185712640 187105280 ⟨⟨59521096437, 59521096440⟩, ⟨58057538066, 60993426659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 237895680 238551040 184320000 185712640 ⟨⟨58823503167, 58823503173⟩, ⟨57364735689, 60291008586⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 237895680 238551040 185712640 187105280 ⟨⟨59252404694, 59252404699⟩, ⟨57791892799, 60721659966⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 238551040 181534720 187105280 t = true :=
  ⟨_, (join_su (m := 237240320) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 236584960) (by decide) (join_sr (m := 182927360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 182927360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 236584960) (by decide) (join_sr (m := 185712640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 185712640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 184320000) (by decide) (join_su (m := 237895680) (by decide) (join_sr (m := 182927360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 182927360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 237895680) (by decide) (join_sr (m := 185712640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 185712640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (91/320 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (571/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((187105280 : ℤ) : ℝ) / (D : ℝ)) = (571/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

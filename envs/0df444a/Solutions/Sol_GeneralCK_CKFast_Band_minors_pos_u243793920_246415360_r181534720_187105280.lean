-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_246415360_r181534720_187105280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:04:12.353354+00:00
-- url     : https://prove2.me/submissions/cd14f62c-a4df-4d9d-9d19-7f5043547887

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 47/160]`, `ρ ∈ [277/1280, 571/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 243793920 244449280 181534720 182927360 ⟨⟨55627098213, 55627098216⟩, ⟨54198484042, 57064190285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 243793920 244449280 182927360 184320000 ⟨⟨56040038526, 56040038529⟩, ⟨54609718839, 57478841830⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 244449280 245104640 181534720 182927360 ⟨⟨55370646522, 55370646527⟩, ⟨53944926127, 56804818000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244449280 245104640 182927360 184320000 ⟨⟨55781788246, 55781788253⟩, ⟨54354366726, 57217666594⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243793920 244449280 184320000 185712640 ⟨⟨56452812457, 56452812460⟩, ⟨55020787537, 57893326700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 243793920 244449280 185712640 187105280 ⟨⟨56865420391, 56865420394⟩, ⟨55431690519, 58307645283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 244449280 245104640 184320000 185712640 ⟨⟨56192765736, 56192765742⟩, ⟨54763643358, 57630350673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 244449280 245104640 185712640 187105280 ⟨⟨56603579369, 56603579375⟩, ⟨55172756402, 58042870619⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 245104640 245760000 181534720 182927360 ⟨⟨55114843269, 55114843276⟩, ⟨53692003242, 56546107726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 245104640 245760000 182927360 184320000 ⟨⟨55524189602, 55524189609⟩, ⟨54099652833, 56957156570⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245760000 246415360 181534720 182927360 ⟨⟨54859683732, 54859683739⟩, ⟨53439710757, 56288054648⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245760000 246415360 182927360 184320000 ⟨⟨55267237851, 55267237856⟩, ⟨53845572513, 56697306923⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 245104640 245760000 184320000 185712640 ⟨⟨55933373824, 55933373830⟩, ⟨54507140569, 57368043037⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245104640 245760000 185712640 187105280 ⟨⟨56342396307, 56342396314⟩, ⟨54914466822, 57778767501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245760000 246415360 184320000 185712640 ⟨⟨55674631961, 55674631967⟩, ⟨54251274503, 57106398938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245760000 246415360 185712640 187105280 ⟨⟨56081866428, 56081866435⟩, ⟨54656817093, 57515331059⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 246415360 181534720 187105280 t = true :=
  ⟨_, (join_su (m := 245104640) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 244449280) (by decide) (join_sr (m := 182927360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 182927360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 244449280) (by decide) (join_sr (m := 185712640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 185712640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 184320000) (by decide) (join_su (m := 245760000) (by decide) (join_sr (m := 182927360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 182927360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 245760000) (by decide) (join_sr (m := 185712640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 185712640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (571/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((187105280 : ℤ) : ℝ) / (D : ℝ)) = (571/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_162529280_r201850880_213647360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:53:37.477722+00:00
-- url     : https://prove2.me/submissions/7aff9e8d-b1b3-4990-9718-c1bfde2d212f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 31/160]`, `ρ ∈ [77/320, 163/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 158597120 201850880 204800000 ⟨⟨107814768269, 107814768278⟩, ⟨103749892012, 111937976282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157286400 158597120 204800000 207749120 ⟨⟨109242633855, 109242633862⟩, ⟨105168374849, 113375165923⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 158597120 159907840 201850880 204800000 ⟨⟨106935105016, 106935105024⟩, ⟨102894811924, 111033175773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 158597120 159907840 204800000 207749120 ⟨⟨108353244793, 108353244801⟩, ⟨104303589817, 112460622371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 157286400 158597120 207749120 210698240 ⟨⟨110667318717, 110667318724⟩, ⟨106583716275, 114809134960⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 157286400 158597120 210698240 213647360 ⟨⟨112088847731, 112088847738⟩, ⟨107995940776, 116239908666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 158597120 159907840 207749120 210698240 ⟨⟨109768268937, 109768268946⟩, ⟨105709290368, 113884914486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 158597120 159907840 210698240 213647360 ⟨⟨111180201620, 111180201627⟩, ⟨107111937365, 115306076665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 159907840 161218560 201850880 204800000 ⟨⟨106063151356, 106063151361⟩, ⟨102047121872, 110136413581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 159907840 161218560 204800000 207749120 ⟨⟨107471610243, 107471610248⟩, ⟨103446240598, 111554161092⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 161218560 162529280 201850880 204800000 ⟨⟨105198771908, 105198771916⟩, ⟨101206692728, 109247547881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 161218560 162529280 204800000 207749120 ⟨⟨106597594515, 106597594523⟩, ⟨102596197709, 110655639992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 159907840 161218560 207749120 210698240 ⟨⟨108877017364, 108877017367⟩, ⟨104842344838, 112968818992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 159907840 161218560 210698240 213647360 ⟨⟨110279396198, 110279396201⟩, ⟨106235457711, 114380411124⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 161218560 162529280 207749120 210698240 ⟨⟨107993428016, 107993428023⟩, ⟨103982749881, 112060706140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 161218560 162529280 210698240 213647360 ⟨⟨109386295224, 109386295231⟩, ⟨105366371708, 113462769489⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 162529280 201850880 213647360 t = true :=
  ⟨_, (join_su (m := 159907840) (by decide) (join_sr (m := 207749120) (by decide) (join_su (m := 158597120) (by decide) (join_sr (m := 204800000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 204800000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 158597120) (by decide) (join_sr (m := 210698240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 210698240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 207749120) (by decide) (join_su (m := 161218560) (by decide) (join_sr (m := 204800000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 204800000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 161218560) (by decide) (join_sr (m := 210698240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 210698240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (77/320 : ℝ) (163/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e3 : (((213647360 : ℤ) : ℝ) / (D : ℝ)) = (163/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

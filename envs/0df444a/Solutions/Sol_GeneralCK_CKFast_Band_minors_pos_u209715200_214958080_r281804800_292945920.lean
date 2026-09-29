-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_214958080_r281804800_292945920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:47:22.772375+00:00
-- url     : https://prove2.me/submissions/f424eb25-61fd-48cd-b4cc-c5f5d644b020

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 41/160]`, `ρ ∈ [43/128, 447/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 211025920 281804800 284590080 ⟨⟨106080359184, 106080359191⟩, ⟨102619291014, 109582769953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 209715200 211025920 284590080 287375360 ⟨⟨107059721142, 107059721150⟩, ⟨103591246073, 110569556883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 211025920 212336640 281804800 284590080 ⟨⟨105215609749, 105215609755⟩, ⟨101770452086, 108701847980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 211025920 212336640 284590080 287375360 ⟨⟨106187943293, 106187943300⟩, ⟨102735402092, 109681584299⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 209715200 211025920 287375360 290160640 ⟨⟨108038062869, 108038062876⟩, ⟨104562189025, 111555315172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209715200 211025920 290160640 292945920 ⟨⟨109015390024, 109015390030⟩, ⟨105532125480, 112540050528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 211025920 212336640 287375360 290160640 ⟨⟨107159278757, 107159278765⟩, ⟨103699361828, 110660314448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 211025920 212336640 290160640 292945920 ⟨⟨108129621648, 108129621655⟩, ⟨104662336752, 111638043981⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 212336640 213647360 281804800 284590080 ⟨⟨104355552983, 104355552987⟩, ⟨100926155639, 107825771956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 212336640 213647360 284590080 287375360 ⟨⟨105320875018, 105320875021⟩, ⟨101884117778, 108798474254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 213647360 214958080 281804800 284590080 ⟨⟨103500123301, 103500123309⟩, ⟨100086338256, 106954474086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 213647360 214958080 284590080 287375360 ⟨⟨104458450644, 104458450650⟩, ⟨101037329616, 107920158882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 212336640 213647360 287375360 290160640 ⟨⟨106285220740, 106285220741⟩, ⟨102841111104, 109770192465⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 212336640 213647360 290160640 292945920 ⟨⟨107248595500, 107248595503⟩, ⟨103797140926, 110740931984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 213647360 214958080 287375360 290160640 ⟨⟨105415823058, 105415823066⟩, ⟨101987373248, 108884881282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 213647360 214958080 290160640 292945920 ⟨⟨106372245752, 106372245758⟩, ⟨102936474312, 109848646536⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 214958080 281804800 292945920 t = true :=
  ⟨_, (join_su (m := 212336640) (by decide) (join_sr (m := 287375360) (by decide) (join_su (m := 211025920) (by decide) (join_sr (m := 284590080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 284590080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 211025920) (by decide) (join_sr (m := 290160640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 290160640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 287375360) (by decide) (join_su (m := 213647360) (by decide) (join_sr (m := 284590080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 284590080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 213647360) (by decide) (join_sr (m := 290160640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 290160640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (43/128 : ℝ) (447/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  have e3 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

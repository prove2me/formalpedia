-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u180879360_183500800_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:38:19.044527+00:00
-- url     : https://prove2.me/submissions/3b5d8f9f-16a1-4669-9afe-2f11289196c6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [69/320, 7/32]`, `ρ ∈ [277/1280, 147/640]` by 15 cells of the computing
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
theorem cell0 : cellOK 180879360 181534720 181534720 184320000 ⟨⟨84461670430, 84461670437⟩, ⟨82293455256, 86648031067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 181534720 182190080 181534720 184320000 ⟨⟨84112298392, 84112298396⟩, ⟨81950717313, 86291936455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 180879360 181534720 184320000 187105280 ⟨⟨85668001212, 85668001219⟩, ⟨83495085006, 87859052680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 181534720 182190080 184320000 187105280 ⟨⟨85314226520, 85314226525⟩, ⟨83147954339, 87498545900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 182190080 182845440 181534720 184320000 ⟨⟨83764289330, 83764289336⟩, ⟨81609304208, 85937243648⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 182845440 183500800 181534720 184320000 ⟨⟨83417631919, 83417631926⟩, ⟨81269204960, 85583940966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 182190080 182845440 184320000 187105280 ⟨⟨84961825583, 84961825589⟩, ⟨82802159333, 87139451654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 182845440 183500800 184320000 187105280 ⟨⟨84610787019, 84610787027⟩, ⟨82457688952, 86781758206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 180879360 181534720 187105280 189890560 ⟨⟨86872282490, 86872282498⟩, ⟨84694679933, 89068009981⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 181534720 182190080 187105280 189890560 ⟨⟨86514127357, 86514127361⟩, ⟨84343178534, 88703113466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 180879360 182190080 189890560 192675840 ⟨⟨87893095659, 87893095666⟩, ⟨84307492643, 91527030327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 182190080 182845440 187105280 189890560 ⟨⟨86157356539, 86157356547⟩, ⟨83993023407, 88339639990⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 182845440 183500800 187105280 189890560 ⟨⟨85801958605, 85801958613⟩, ⟨83644203460, 87977577770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 182190080 182845440 189890560 192675840 ⟨⟨87350895045, 87350895051⟩, ⟨85181909160, 89537821613⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 182845440 183500800 189890560 192675840 ⟨⟨86991159332, 86991159338⟩, ⟨84828761028, 89171412425⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 180879360 183500800 181534720 192675840 t = true :=
  ⟨_, (join_sr (m := 187105280) (by decide) (join_su (m := 182190080) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 181534720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 181534720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184320000) (by decide) (join_su (m := 182845440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 182845440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 182190080) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 181534720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 189890560) (by decide) (join_su (m := 182845440) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 182845440) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (69/320 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((180879360 : ℤ) : ℝ) / (D : ℝ)) = (69/320 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

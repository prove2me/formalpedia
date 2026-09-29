-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u159907840_162529280_r154664960_166461440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:45:05.703638+00:00
-- url     : https://prove2.me/submissions/070a1dd1-77d9-4c16-a4f3-ac3218a265c2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [61/320, 31/160]`, `ρ ∈ [59/320, 127/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 159907840 160563200 154664960 157614080 ⟨⟨83269074786, 83269074795⟩, ⟨80863700845, 85697066838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 160563200 161218560 154664960 157614080 ⟨⟨82916865458, 82916865465⟩, ⟨80519722441, 85336498336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 159907840 160563200 157614080 160563200 ⟨⟨84732430065, 84732430073⟩, ⟨82321465027, 87165983070⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 160563200 161218560 157614080 160563200 ⟨⟨84374835658, 84374835665⟩, ⟨81972113069, 86800018735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 161218560 161873920 154664960 157614080 ⟨⟨82566318116, 82566318125⟩, ⟨80177351807, 84977647192⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 161873920 162529280 154664960 157614080 ⟨⟨82217417319, 82217417323⟩, ⟨79836574054, 84620497385⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 161218560 161873920 157614080 160563200 ⟨⟨84018919899, 84018919907⟩, ⟨81624385625, 86435788324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 161873920 162529280 157614080 160563200 ⟨⟨83664667248, 83664667251⟩, ⟨81278267708, 86073275718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 159907840 160563200 160563200 163512320 ⟨⟨86192308484, 86192308492⟩, ⟨83775781589, 88631393028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 160563200 161218560 160563200 163512320 ⟨⟨85829366674, 85829366682⟩, ⟨83421093345, 88260070942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 159907840 160563200 163512320 166461440 ⟨⟨87648737443, 87648737451⟩, ⟨85226677616, 90093324421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 160563200 161218560 163512320 166461440 ⟨⟨87280485488, 87280485496⟩, ⟨84866689943, 89716682247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 161218560 161873920 160563200 163512320 ⟨⟨85468119784, 85468119790⟩, ⟨83068045973, 87890498950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 161873920 162529280 160563200 163512320 ⟨⟨85108552178, 85108552182⟩, ⟨82716624392, 87522660844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 161218560 161873920 163512320 166461440 ⟨⟨86913944341, 86913944349⟩, ⟨84508359125, 89341805944⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 161873920 162529280 163512320 166461440 ⟨⟨86549098278, 86549098281⟩, ⟨84151669984, 88968679227⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 159907840 162529280 154664960 166461440 t = true :=
  ⟨_, (join_sr (m := 160563200) (by decide) (join_su (m := 161218560) (by decide) (join_sr (m := 157614080) (by decide) (join_su (m := 160563200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 160563200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 157614080) (by decide) (join_su (m := 161873920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 161873920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 161218560) (by decide) (join_sr (m := 163512320) (by decide) (join_su (m := 160563200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 160563200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 163512320) (by decide) (join_su (m := 161873920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 161873920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (61/320 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (59/320 : ℝ) (127/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e3 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

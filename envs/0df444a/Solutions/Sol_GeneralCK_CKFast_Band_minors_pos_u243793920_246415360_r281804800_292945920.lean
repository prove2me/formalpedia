-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_246415360_r281804800_292945920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:27:15.238683+00:00
-- url     : https://prove2.me/submissions/7217a754-5edb-4872-a2b4-1816e245a856

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 47/160]`, `ρ ∈ [43/128, 447/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 243793920 244449280 281804800 284590080 ⟨⟨85156733657, 85156733660⟩, ⟨83358953970, 86966868063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 244449280 245104640 281804800 284590080 ⟨⟨84775091826, 84775091833⟩, ⟨82981763358, 86580733192⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 243793920 244449280 284590080 287375360 ⟨⟨85960259656, 85960259659⟩, ⟨84158870311, 87774012696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244449280 245104640 284590080 287375360 ⟨⟨85575303817, 85575303824⟩, ⟨83778374005, 87384555624⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 245104640 245760000 281804800 284590080 ⟨⟨84394277696, 84394277702⟩, ⟨82605382863, 86195443825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 245760000 246415360 281804800 284590080 ⟨⟨84014285634, 84014285641⟩, ⟨82229806967, 85810994210⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 245104640 245760000 284590080 287375360 ⟨⟨85191179258, 85191179265⟩, ⟨83398691408, 86995947614⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 245760000 246415360 284590080 287375360 ⟨⟨84807880330, 84807880336⟩, ⟨83019816988, 86608182905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 244449280 287375360 290160640 ⟨⟨86763226060, 86763226062⟩, ⟨84958228706, 88580596035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 244449280 245104640 287375360 290160640 ⟨⟨86374963164, 86374963171⟩, ⟨84574433600, 88187823769⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243793920 244449280 290160640 292945920 ⟨⟨87565635562, 87565635565⟩, ⟨85757031838, 89386620784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 244449280 245104640 290160640 292945920 ⟨⟨87174072520, 87174072527⟩, ⟨85369944784, 88990540289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 245104640 245760000 287375360 290160640 ⟨⟨85987535059, 85987535066⟩, ⟨84191455729, 87795904058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245760000 246415360 287375360 290160640 ⟨⟨85600936084, 85600936091⟩, ⟨83809289548, 87404831129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245104640 245760000 290160640 292945920 ⟨⟨86783347714, 86783347721⟩, ⟨84983678429, 88595315779⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245760000 246415360 290160640 292945920 ⟨⟨86393455471, 86393455477⟩, ⟨84598227212, 88200941464⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 246415360 281804800 292945920 t = true :=
  ⟨_, (join_sr (m := 287375360) (by decide) (join_su (m := 245104640) (by decide) (join_sr (m := 284590080) (by decide) (join_su (m := 244449280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 244449280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 284590080) (by decide) (join_su (m := 245760000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 245760000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 245104640) (by decide) (join_sr (m := 290160640) (by decide) (join_su (m := 244449280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 244449280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 290160640) (by decide) (join_su (m := 245760000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 245760000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (43/128 : ℝ) (447/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  have e3 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

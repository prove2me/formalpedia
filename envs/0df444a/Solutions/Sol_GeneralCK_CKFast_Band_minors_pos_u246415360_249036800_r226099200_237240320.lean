-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_249036800_r226099200_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:54:53.888753+00:00
-- url     : https://prove2.me/submissions/bb9c2915-9be1-4074-b528-e3c7fdc44b1b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 19/64]`, `ρ ∈ [69/256, 181/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247070720 226099200 228884480 ⟨⟨67713541623, 67713541630⟩, ⟨66005301849, 69433771245⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 247070720 247726080 226099200 228884480 ⟨⟨67402637724, 67402637729⟩, ⟨65698600391, 69118621880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246415360 247070720 228884480 231669760 ⟨⟨68515022645, 68515022652⟩, ⟨66803176083, 70238869453⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247070720 247726080 228884480 231669760 ⟨⟨68200676871, 68200676876⟩, ⟨66493042255, 69920268808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 247726080 248381440 226099200 228884480 ⟨⟨67092454523, 67092454528⟩, ⟨65392602375, 68804210718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 248381440 249036800 226099200 228884480 ⟨⟨66782986940, 66782986945⟩, ⟨65087302836, 68490532559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247726080 248381440 228884480 231669760 ⟨⟨67887056711, 67887056718⟩, ⟨66183616783, 69602411281⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 248381440 249036800 228884480 231669760 ⟨⟨67574157061, 67574157068⟩, ⟨65874894679, 69285291645⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 246415360 247070720 231669760 234455040 ⟨⟨69315918918, 69315918924⟩, ⟨67600467180, 71043381253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 247070720 247726080 231669760 234455040 ⟨⟨68998138765, 68998138767⟩, ⟨67286908416, 70721336880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 246415360 247070720 234455040 237240320 ⟨⟨70116233158, 70116233163⟩, ⟨68397177849, 71847309368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 247070720 247726080 234455040 237240320 ⟨⟨69795026074, 69795026078⟩, ⟨68080201540, 71521828781⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 247726080 248381440 231669760 234455040 ⟨⟨68681089065, 68681089071⟩, ⟨66974062850, 70400040465⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 248381440 249036800 231669760 234455040 ⟨⟨68364764692, 68364764697⟩, ⟨66661925468, 70079486757⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 247726080 248381440 234455040 237240320 ⟨⟨69474554213, 69474554219⟩, ⟨67763943198, 71197100914⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 248381440 249036800 234455040 237240320 ⟨⟨69154812422, 69154812427⟩, ⟨67448397783, 70873120495⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 249036800 226099200 237240320 t = true :=
  ⟨_, (join_sr (m := 231669760) (by decide) (join_su (m := 247726080) (by decide) (join_sr (m := 228884480) (by decide) (join_su (m := 247070720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 247070720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 228884480) (by decide) (join_su (m := 248381440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 248381440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 247726080) (by decide) (join_sr (m := 234455040) (by decide) (join_su (m := 247070720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 247070720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 234455040) (by decide) (join_su (m := 248381440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 248381440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (69/256 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

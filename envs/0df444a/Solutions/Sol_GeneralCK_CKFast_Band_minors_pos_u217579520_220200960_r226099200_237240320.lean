-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u217579520_220200960_r226099200_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:13:40.722242+00:00
-- url     : https://prove2.me/submissions/76131577-43ff-4fcc-b357-86f84951c9a4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [83/320, 21/80]`, `ρ ∈ [69/256, 181/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 217579520 218234880 226099200 228884480 ⟨⟨82191260917, 82191260920⟩, ⟨80279039734, 84117640260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 218234880 218890240 226099200 228884480 ⟨⟨81842977418, 81842977425⟩, ⟨79935852289, 83764204686⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 217579520 218234880 228884480 231669760 ⟨⟨83149446424, 83149446427⟩, ⟨81233204842, 85079850410⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 218234880 218890240 228884480 231669760 ⟨⟨82797478776, 82797478782⟩, ⟨80886342416, 84722721709⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 218890240 219545600 226099200 228884480 ⟨⟨81495681562, 81495681569⟩, ⟨79593628834, 83411780758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 219545600 220200960 226099200 228884480 ⟨⟨81149366175, 81149366181⟩, ⟨79252362369, 83060361122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 218890240 219545600 228884480 231669760 ⟨⟨82446504858, 82446504865⟩, ⟨80540450085, 84366610719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 219545600 220200960 228884480 231669760 ⟨⟨82096517468, 82096517475⟩, ⟨80195520823, 84011510062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 217579520 218234880 231669760 234455040 ⟨⟨84106632694, 84106632696⟩, ⟨82186375819, 86041056135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 218234880 218890240 231669760 234455040 ⟨⟨83750992396, 83750992402⟩, ⟨81835849812, 85680245908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 218234880 234455040 237240320 ⟨⟨85062825016, 85062825019⟩, ⟨83138557924, 87001262759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 218234880 218890240 234455040 237240320 ⟨⟨84703523491, 84703523498⟩, ⟨82784379656, 86636782530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 218890240 219545600 231669760 234455040 ⟨⟨83396351807, 83396351813⟩, ⟨81486299896, 85320459350⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 219545600 220200960 231669760 234455040 ⟨⟨83042703700, 83042703706⟩, ⟨81137719020, 84961689054⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 218890240 219545600 234455040 237240320 ⟨⟨84345227547, 84345227553⟩, ⟨82431183371, 86273331817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 219545600 220200960 234455040 237240320 ⟨⟨83987929930, 83987929936⟩, ⟨82078961992, 85910903191⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 217579520 220200960 226099200 237240320 t = true :=
  ⟨_, (join_sr (m := 231669760) (by decide) (join_su (m := 218890240) (by decide) (join_sr (m := 228884480) (by decide) (join_su (m := 218234880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 218234880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 228884480) (by decide) (join_su (m := 219545600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 219545600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 218890240) (by decide) (join_sr (m := 234455040) (by decide) (join_su (m := 218234880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 218234880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 234455040) (by decide) (join_su (m := 219545600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 219545600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (83/320 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (69/256 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

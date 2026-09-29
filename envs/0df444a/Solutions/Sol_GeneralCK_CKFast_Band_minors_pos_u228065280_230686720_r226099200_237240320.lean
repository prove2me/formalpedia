-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u228065280_230686720_r226099200_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:29:55.201973+00:00
-- url     : https://prove2.me/submissions/2d877f2b-4c88-41b9-a15b-78c0477afcf6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [87/320, 11/40]`, `ρ ∈ [69/256, 181/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 228065280 228720640 226099200 228884480 ⟨⟨76733331272, 76733331278⟩, ⟨74899904695, 78580060193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 228720640 229376000 226099200 228884480 ⟨⟨76400021632, 76400021638⟩, ⟨74571332978, 78241961887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 228065280 228720640 228884480 231669760 ⟨⟨77633285446, 77633285452⟩, ⟨75795986996, 79483893206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 228720640 229376000 228884480 231669760 ⟨⟨77296385755, 77296385760⟩, ⟨75463834614, 79142195612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 229376000 230031360 226099200 228884480 ⟨⟨76067591686, 76067591691⟩, ⟨74243619934, 77904764600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230031360 230686720 226099200 228884480 ⟨⟨75736035139, 75736035145⟩, ⟨73916759430, 77568461884⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 229376000 230031360 228884480 231669760 ⟨⟨76960371406, 76960371413⟩, ⟨75132546568, 78801404672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 230031360 230686720 228884480 231669760 ⟨⟨76625236081, 76625236088⟩, ⟨74802116690, 78461513915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 228065280 228720640 231669760 234455040 ⟨⟨78532411867, 78532411873⟩, ⟨76691245161, 80386894780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 228720640 229376000 231669760 234455040 ⟨⟨78191931995, 78191932001⟩, ⟨76355521903, 80041607851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 228720640 234455040 237240320 ⟨⟨79430714705, 79430714712⟩, ⟨77585683342, 81289069106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228720640 229376000 234455040 237240320 ⟨⟨79086664461, 79086664468⟩, ⟨77246398933, 80940202736⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 229376000 230031360 231669760 234455040 ⟨⟨77852343021, 77852343027⟩, ⟨76020668546, 79697233120⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 230031360 230686720 231669760 234455040 ⟨⟨77513638598, 77513638604⟩, ⟨75686678894, 79353764087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 229376000 230031360 234455040 237240320 ⟨⟨78743510575, 78743510581⟩, ⟨76907989895, 80592254010⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 230031360 230686720 234455040 237240320 ⟨⟨78401246677, 78401246682⟩, ⟨76570450010, 80245216404⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 228065280 230686720 226099200 237240320 t = true :=
  ⟨_, (join_sr (m := 231669760) (by decide) (join_su (m := 229376000) (by decide) (join_sr (m := 228884480) (by decide) (join_su (m := 228720640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 228720640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 228884480) (by decide) (join_su (m := 230031360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 230031360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 229376000) (by decide) (join_sr (m := 234455040) (by decide) (join_su (m := 228720640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 228720640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 234455040) (by decide) (join_su (m := 230031360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 230031360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (87/320 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (69/256 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

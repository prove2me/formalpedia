-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_178257920_r437780480_460062720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:04:12.112898+00:00
-- url     : https://prove2.me/submissions/1576c4ae-d4c8-4d58-91ae-7bd8484de009

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 17/80]`, `ρ ∈ [167/320, 351/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 170393600 437780480 443351040 ⟨⟨201792693286, 201792693295⟩, ⟨192897377754, 210882789579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 167772160 170393600 443351040 448921600 ⟨⟨204027038383, 204027038393⟩, ⟨195103887135, 213144489498⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 170393600 173015040 437780480 443351040 ⟨⟨198937176788, 198937176798⟩, ⟨190127884374, 207939323273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 170393600 173015040 443351040 448921600 ⟨⟨201147922939, 201147922948⟩, ⟨192310681437, 210177579072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 167772160 170393600 448921600 454492160 ⟨⟨206256109023, 206256109032⟩, ⟨197305229083, 215400802581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 167772160 170393600 454492160 460062720 ⟨⟨208479978090, 208479978100⟩, ⟨199501474741, 217651803469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 170393600 173015040 448921600 454492160 ⟨⟨203353573483, 203353573492⟩, ⟨194488485453, 212410631310⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 170393600 173015040 454492160 460062720 ⟨⟨205554198127, 205554198135⟩, ⟨196661364485, 214638551344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 173015040 175636480 437780480 443351040 ⟨⟨196112085877, 196112085886⟩, ⟨187387324772, 205027804240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 173015040 175636480 443351040 448921600 ⟨⟨198299182466, 198299182476⟩, ⟨189546375316, 207242547293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 175636480 178257920 437780480 443351040 ⟨⟨193316620913, 193316620919⟩, ⟨184674939607, 202147392089⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 175636480 178257920 443351040 448921600 ⟨⟨195480022393, 195480022397⟩, ⟨186810213758, 204338559640⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 173015040 175636480 448921600 454492160 ⟨⟨200481357922, 200481357932⟩, ⟨191700602860, 209452265658⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 173015040 175636480 454492160 460062720 ⟨⟨202658678887, 202658678897⟩, ⟨193850072504, 211657027539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 175636480 178257920 448921600 454492160 ⟨⟨197638672884, 197638672889⟩, ⟨188940830675, 206524877022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 175636480 178257920 454492160 460062720 ⟨⟨199792636090, 199792636096⟩, ⟨191066852609, 208706409407⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 178257920 437780480 460062720 t = true :=
  ⟨_, (join_su (m := 173015040) (by decide) (join_sr (m := 448921600) (by decide) (join_su (m := 170393600) (by decide) (join_sr (m := 443351040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 443351040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 170393600) (by decide) (join_sr (m := 454492160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 454492160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 448921600) (by decide) (join_su (m := 175636480) (by decide) (join_sr (m := 443351040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 443351040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 175636480) (by decide) (join_sr (m := 454492160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 454492160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (167/320 : ℝ) (351/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  have e3 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

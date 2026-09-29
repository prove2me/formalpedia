-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u183500800_188743680_r237240320_248381440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:18:59.58327+00:00
-- url     : https://prove2.me/submissions/2768de7e-1afe-4695-9ae1-e63b63d7c99e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/32, 9/40]`, `ρ ∈ [181/640, 379/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 183500800 184811520 237240320 240025600 ⟨⟨106275194639, 106275194645⟩, ⟨102587627529, 110010230217⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 183500800 184811520 240025600 242810880 ⟨⟨107425031119, 107425031125⟩, ⟨103729398938, 111168125183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 184811520 186122240 237240320 240025600 ⟨⟨105423522685, 105423522692⟩, ⟨101755090735, 109139056778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 184811520 186122240 240025600 242810880 ⟨⟨106565441745, 106565441753⟩, ⟨102888967560, 110289013371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 183500800 184811520 242810880 245596160 ⟨⟨108573148543, 108573148551⟩, ⟨104869469051, 112324282935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 183500800 184811520 245596160 248381440 ⟨⟨109719557728, 109719557735⟩, ⟨106007848558, 113478714419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 184811520 186122240 242810880 245596160 ⟨⟨107705677451, 107705677458⟩, ⟨104021178260, 111437268983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 184811520 186122240 245596160 248381440 ⟨⟨108844240315, 108844240322⟩, ⟨105151733227, 112583834253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 186122240 187432960 237240320 240025600 ⟨⟨104577752805, 104577752808⟩, ⟨100928244322, 108274002215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 186122240 187432960 240025600 242810880 ⟨⟨105711781773, 105711781777⟩, ⟨102054254322, 109416047278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 187432960 188743680 237240320 240025600 ⟨⟨103737793888, 103737793896⟩, ⟨100107000713, 107414971802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 187432960 188743680 240025600 242810880 ⟨⟨104863959923, 104863959931⟩, ⟨101225171461, 108549132024⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 186122240 187432960 242810880 245596160 ⟨⟨106844162447, 106844162451⟩, ⟨103178632739, 110556426942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 186122240 187432960 245596160 248381440 ⟨⟨107974905051, 107974905053⟩, ⟨104301389682, 111695151556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 187432960 188743680 242810880 245596160 ⟨⟨105988512099, 105988512105⟩, ⟨102341744554, 109681661800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 187432960 188743680 245596160 248381440 ⟨⟨107111460355, 107111460362⟩, ⟨103456729821, 110812571185⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 183500800 188743680 237240320 248381440 t = true :=
  ⟨_, (join_su (m := 186122240) (by decide) (join_sr (m := 242810880) (by decide) (join_su (m := 184811520) (by decide) (join_sr (m := 240025600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 240025600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 184811520) (by decide) (join_sr (m := 245596160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 245596160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 242810880) (by decide) (join_su (m := 187432960) (by decide) (join_sr (m := 240025600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 240025600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 187432960) (by decide) (join_sr (m := 245596160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 245596160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/32 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (181/640 : ℝ) (379/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e3 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

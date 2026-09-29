-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_228065280_r237240320_248381440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:34:56.619973+00:00
-- url     : https://prove2.me/submissions/8f4b8398-2a7b-4b1e-a3cd-0c7d0ef8a84f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 87/320]`, `ρ ∈ [181/640, 379/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226099200 237240320 240025600 ⟨⟨81727788552, 81727788558⟩, ⟨79859583442, 83609527050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 226099200 226754560 237240320 240025600 ⟨⟨81376505800, 81376505806⟩, ⟨79513161081, 83253332549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 225443840 226099200 240025600 242810880 ⟨⟨82638713661, 82638713668⟩, ⟨80766614951, 84524351822⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226099200 226754560 240025600 242810880 ⟨⟨82283858629, 82283858634⟩, ⟨80416629304, 84164576205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 226754560 227409920 237240320 240025600 ⟨⟨81026150869, 81026150875⟩, ⟨79167644954, 82898087765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 227409920 228065280 237240320 240025600 ⟨⟨80676717158, 80676717161⟩, ⟨78823028616, 82543785937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 226754560 227409920 240025600 242810880 ⟨⟨81929936786, 81929936792⟩, ⟨80067555280, 83805755657⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 227409920 228065280 240025600 242810880 ⟨⟨81576941512, 81576941515⟩, ⟨79719386404, 83447883395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 226099200 242810880 245596160 ⟨⟨83548788168, 83548788176⟩, ⟨81672799729, 85438322047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 226099200 226754560 242810880 245596160 ⟨⟨83190370851, 83190370856⟩, ⟨81319260709, 85074975396⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 225443840 226099200 245596160 248381440 ⟨⟨84458016423, 84458016429⟩, ⟨82578142106, 86351442097⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 226099200 226754560 245596160 248381440 ⟨⟨84096046754, 84096046760⟩, ⟨82221059560, 85984534433⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 226754560 227409920 242810880 245596160 ⟨⟨82832892000, 82832892007⟩, ⟨80966638603, 84712589074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 227409920 228065280 242810880 245596160 ⟨⟨82476344972, 82476344975⟩, ⟨80614926916, 84351156273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 226754560 227409920 245596160 248381440 ⟨⟨83735020736, 83735020741⟩, ⟨81864899129, 85618592260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 227409920 228065280 245596160 248381440 ⟨⟨83374931700, 83374931701⟩, ⟨81509654295, 85253608750⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 228065280 237240320 248381440 t = true :=
  ⟨_, (join_sr (m := 242810880) (by decide) (join_su (m := 226754560) (by decide) (join_sr (m := 240025600) (by decide) (join_su (m := 226099200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 226099200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 240025600) (by decide) (join_su (m := 227409920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 227409920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 226754560) (by decide) (join_sr (m := 245596160) (by decide) (join_su (m := 226099200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 226099200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 245596160) (by decide) (join_su (m := 227409920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 227409920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (87/320 : ℝ) →
    rho ∈ Set.Icc (181/640 : ℝ) (379/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e2 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e3 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

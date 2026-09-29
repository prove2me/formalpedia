-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_128450560_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:02:34.381569+00:00
-- url     : https://prove2.me/submissions/2f0b4ce7-d490-4d90-a74d-6428aa8cea4d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 49/320]`, `ρ ∈ [91/640, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 125829120 126484480 119275520 122224640 ⟨⟨82608455873, 82608455879⟩, ⟨79759888683, 85489473595⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 126484480 127139840 119275520 122224640 ⟨⟨82224871808, 82224871817⟩, ⟨79388295618, 85093660628⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 125829120 126484480 122224640 125173760 ⟨⟨84455675475, 84455675477⟩, ⟨81600355929, 87343351220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 126484480 127139840 122224640 125173760 ⟨⟨84064827632, 84064827639⟩, ⟨81221510434, 86940265114⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 127139840 127795200 119275520 122224640 ⟨⟨81843779593, 81843779600⟩, ⟨79019092403, 84700444262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 127795200 128450560 119275520 122224640 ⟨⟨81465150175, 81465150182⟩, ⟨78652251327, 84309794068⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 127139840 127795200 122224640 125173760 ⟨⟨83676503763, 83676503770⟩, ⟨80845087162, 86539807447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 127795200 128450560 122224640 125173760 ⟨⟨83290674585, 83290674592⟩, ⟨80471058167, 86141947561⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 125829120 126484480 125173760 128122880 ⟨⟨86295986991, 86295986996⟩, ⟨83433985460, 89190250291⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 126484480 127139840 125173760 128122880 ⟨⟨85897954125, 85897954135⟩, ⟨83047965307, 88779970774⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 125829120 126484480 128122880 131072000 ⟨⟨88129462450, 88129462453⟩, ⟨85260848190, 91030243947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 126484480 127139840 128122880 131072000 ⟨⟨87724322115, 87724322124⟩, ⟨84867729980, 90612849522⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 127139840 127795200 125173760 128122880 ⟨⟨85502476414, 85502476422⟩, ⟨82664398823, 88372350572⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 127795200 128450560 125173760 128122880 ⟨⟨85109524348, 85109524357⟩, ⟨82283257826, 87967358815⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 127139840 127795200 128122880 131072000 ⟨⟨87321767188, 87321767195⟩, ⟨84477095965, 90198144350⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 127795200 128450560 128122880 131072000 ⟨⟨86921767947, 86921767956⟩, ⟨84088917746, 89786097359⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 128450560 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 127139840) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 126484480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 126484480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 122224640) (by decide) (join_su (m := 127795200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 127795200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 127139840) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 126484480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 126484480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 128122880) (by decide) (join_su (m := 127795200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 127795200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (49/320 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((128450560 : ℤ) : ℝ) / (D : ℝ)) = (49/320 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

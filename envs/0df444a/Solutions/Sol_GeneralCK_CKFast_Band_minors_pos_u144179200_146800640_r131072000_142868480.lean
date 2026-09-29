-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u144179200_146800640_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:28:27.383986+00:00
-- url     : https://prove2.me/submissions/f8abaabe-3440-4c7b-ad4b-7a3cf57b0448

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/64, 7/40]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 144179200 144834560 131072000 134021120 ⟨⟨79314323916, 79314323924⟩, ⟨76741736757, 81913411272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 144834560 145489920 131072000 134021120 ⟨⟨78965394009, 78965394017⟩, ⟨76402440689, 81554677531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 144179200 144834560 134021120 136970240 ⟨⟨80949743448, 80949743457⟩, ⟨78370978375, 83554957055⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 144834560 145489920 134021120 136970240 ⟨⟨80594587290, 80594587298⟩, ⟨78025469234, 83189985050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 145489920 146145280 131072000 134021120 ⟨⟨78618388868, 78618388871⟩, ⟨76064997913, 81197941753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 146145280 146800640 131072000 134021120 ⟨⟨78273288600, 78273288608⟩, ⟨75729389373, 80843183199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 145489920 146145280 134021120 136970240 ⟨⟨80241379493, 80241379496⟩, ⟨77681837100, 82827034464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 146145280 146800640 134021120 136970240 ⟨⟨79890100006, 79890100014⟩, ⟨77340062750, 82466084407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 144179200 144834560 136970240 139919360 ⟨⟨82580319254, 82580319261⟩, ⟨79995421182, 85191614004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 144834560 145489920 136970240 139919360 ⟨⟨82218990564, 82218990571⟩, ⟨79643752063, 84820458080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 144179200 144834560 139919360 142868480 ⟨⟨84206094633, 84206094640⟩, ⟨81615107908, 86823425997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 144834560 145489920 139919360 142868480 ⟨⟨83838646445, 83838646452⟩, ⟨81257331231, 86446139801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 145489920 146145280 136970240 139919360 ⟨⟨81859633233, 81859633235⟩, ⟨79293983073, 84451346426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 146145280 146800640 136970240 139919360 ⟨⟨81502227057, 81502227063⟩, ⟨78946094833, 84084258004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 145489920 146145280 139919360 142868480 ⟨⟨83473192025, 83473192029⟩, ⟨80901477225, 86070920129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 146145280 146800640 139919360 142868480 ⟨⟨83109711025, 83109711032⟩, ⟨80547526362, 85697745804⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 144179200 146800640 131072000 142868480 t = true :=
  ⟨_, (join_sr (m := 136970240) (by decide) (join_su (m := 145489920) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 144834560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 144834560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 134021120) (by decide) (join_su (m := 146145280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 146145280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 145489920) (by decide) (join_sr (m := 139919360) (by decide) (join_su (m := 144834560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 144834560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 139919360) (by decide) (join_su (m := 146145280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 146145280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/64 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((144179200 : ℤ) : ℝ) / (D : ℝ)) = (11/64 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

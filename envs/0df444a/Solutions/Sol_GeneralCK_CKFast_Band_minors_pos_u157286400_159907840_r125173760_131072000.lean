-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_159907840_r125173760_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:29:40.077986+00:00
-- url     : https://prove2.me/submissions/0037148e-59b7-43a3-ac6b-e04b9c7f9f60

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 61/320]`, `ρ ∈ [191/1280, 5/32]` by 12 cells of the computing
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
theorem cell0 : cellOK 157286400 157941760 125173760 126648320 ⟨⟨69256473681, 69256473688⟩, ⟨67344519471, 71183381238⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157286400 157941760 126648320 128122880 ⟨⟨70018987102, 70018987108⟩, ⟨68104385791, 71948536480⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157941760 158597120 125173760 126648320 ⟨⟨68955722047, 68955722054⟩, ⟨67049753560, 70876562102⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 157941760 158597120 126648320 128122880 ⟨⟨69715288762, 69715288769⟩, ⟨67806679865, 71638764168⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 157286400 157941760 128122880 131072000 ⟨⟨71160900648, 71160900654⟩, ⟨68774225223, 73571010672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 157941760 158597120 128122880 131072000 ⟨⟨70852803058, 70852803066⟩, ⟨68474460336, 73254439991⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 158597120 159252480 125173760 126648320 ⟨⟨68656496050, 68656496053⟩, ⟨66756470613, 70571312048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 158597120 159252480 126648320 128122880 ⟨⟨69413126954, 69413126956⟩, ⟨67510467807, 71330571821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 159252480 159907840 125173760 126648320 ⟨⟨68358780769, 68358780776⟩, ⟨66464656176, 70267615695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 159252480 159907840 126648320 128122880 ⟨⟨69112486679, 69112486685⟩, ⟨67215735086, 71023943978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 158597120 159252480 128122880 131072000 ⟨⟨70546258113, 70546258116⟩, ⟨68176190943, 72939480432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 159252480 159907840 128122880 131072000 ⟨⟨70241250700, 70241250708⟩, ⟨67879402554, 72626116257⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 159907840 125173760 131072000 t = true :=
  ⟨_, (join_su (m := 158597120) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 157941760) (by decide) (join_sr (m := 126648320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 126648320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 157941760) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 128122880) (by decide) (join_su (m := 159252480) (by decide) (join_sr (m := 126648320) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 126648320) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 159252480) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (61/320 : ℝ) →
    rho ∈ Set.Icc (191/1280 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e2 : (((125173760 : ℤ) : ℝ) / (D : ℝ)) = (191/1280 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

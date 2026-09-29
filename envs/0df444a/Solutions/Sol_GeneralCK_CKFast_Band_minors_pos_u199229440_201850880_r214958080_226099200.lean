-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_201850880_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:25:53.086356+00:00
-- url     : https://prove2.me/submissions/2dcd3310-5a46-41a4-9a3d-bcf0cae849cf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 77/320]`, `ρ ∈ [41/160, 69/256]` by 9 cells of the computing
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
theorem cell0 : cellOK 199229440 200540160 214958080 217743360 ⟨⟨87923873407, 87923873410⟩, ⟨84515267396, 91375754550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199229440 200540160 217743360 220528640 ⟨⟨88991392769, 88991392771⟩, ⟨85574921427, 92451154790⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 200540160 201195520 214958080 217743360 ⟨⟨87379958913, 87379958920⟩, ⟨85343397479, 89432275335⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 201195520 201850880 214958080 217743360 ⟨⟨87018823516, 87018823520⟩, ⟨84988006309, 89065328274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 200540160 201850880 217743360 220528640 ⟨⟨88258925045, 88258925052⟩, ⟨84859064354, 91701756349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 199229440 200540160 220528640 223313920 ⟨⟨90057518399, 90057518402⟩, ⟨86633194407, 93525148278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 199229440 200540160 223313920 226099200 ⟨⟨91122258367, 91122258371⟩, ⟨87690094329, 94597743167⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 200540160 201850880 220528640 223313920 ⟨⟨89317242340, 89317242346⟩, ⟨85909558995, 92767912813⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 200540160 201850880 223313920 226099200 ⟨⟨90374204263, 90374204269⟩, ⟨86958710423, 93832701416⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 201850880 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 200540160) (by decide) (join_sr (m := 217743360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 217743360) (by decide) (join_su (m := 201195520) (by decide) (leaf_ok cell2) (leaf_ok cell3)) (leaf_ok cell4))) (join_su (m := 200540160) (by decide) (join_sr (m := 223313920) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 223313920) (by decide) (leaf_ok cell7) (leaf_ok cell8))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (77/320 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

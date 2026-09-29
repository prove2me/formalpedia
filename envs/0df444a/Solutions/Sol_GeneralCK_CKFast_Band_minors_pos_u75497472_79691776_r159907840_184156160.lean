-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u75497472_79691776_r159907840_184156160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:49:21.185489+00:00
-- url     : https://prove2.me/submissions/5ed73e78-fc88-4ac5-87aa-3d0243a90e82

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/100, 19/200]`, `ρ ∈ [61/320, 281/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 75497472 76546048 159907840 165969920 ⟨⟨157101350866, 157101350879⟩, ⟨149395915287, 164993657104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 76546048 77594624 159907840 165969920 ⟨⟨155747098840, 155747098853⟩, ⟨148116107725, 163562043797⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 75497472 76546048 165969920 172032000 ⟨⟨161805760451, 161805760463⟩, ⟨154090109299, 169705275375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 76546048 77594624 165969920 172032000 ⟨⟨160426057787, 160426057800⟩, ⟨152784258871, 168248901542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 77594624 78643200 159907840 165969920 ⟨⟨154412601985, 154412601998⟩, ⟨146854654095, 162151656562⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 78643200 79691776 159907840 165969920 ⟨⟨153097372314, 153097372326⟩, ⟨145611106100, 160761965490⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 77594624 78643200 165969920 172032000 ⟨⟨159066181993, 159066182004⟩, ⟨151496862829, 166813793116⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 78643200 79691776 165969920 172032000 ⟨⟨157725649259, 157725649269⟩, ⟨150227475754, 165399425830⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 75497472 76546048 172032000 178094080 ⟨⟨166453241400, 166453241413⟩, ⟨158728327393, 174359064067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 76546048 77594624 172032000 178094080 ⟨⟨165049080033, 165049080046⟩, ⟨157397414787, 172878929941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 75497472 76546048 178094080 184156160 ⟨⟨171045557117, 171045557130⟩, ⟨163312276276, 178956842449⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 76546048 77594624 178094080 184156160 ⟨⟨169617881162, 169617881172⟩, ⟨161957235993, 177453898891⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 77594624 78643200 172032000 178094080 ⟨⟨163664799213, 163664799224⟩, ⟨156085038755, 171420082947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 78643200 79691776 172032000 178094080 ⟨⟨162299919630, 162299919640⟩, ⟨154790757102, 169982004739⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 77594624 78643200 178094080 184156160 ⟨⟨168210122826, 168210122839⟩, ⟨160620797576, 175972248043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 78643200 79691776 178094080 184156160 ⟨⟨166821807576, 166821807588⟩, ⟨159302522363, 174511377701⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 75497472 79691776 159907840 184156160 t = true :=
  ⟨_, (join_sr (m := 172032000) (by decide) (join_su (m := 77594624) (by decide) (join_sr (m := 165969920) (by decide) (join_su (m := 76546048) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 76546048) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 165969920) (by decide) (join_su (m := 78643200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 78643200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 77594624) (by decide) (join_sr (m := 178094080) (by decide) (join_su (m := 76546048) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 76546048) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178094080) (by decide) (join_su (m := 78643200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 78643200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (19/200 : ℝ) →
    rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e1 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e2 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e3 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

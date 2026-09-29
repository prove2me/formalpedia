-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_246415360_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:47:45.416348+00:00
-- url     : https://prove2.me/submissions/2650adee-dcef-4251-94af-a4b58c5699f8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 47/160]`, `ρ ∈ [41/160, 69/256]` by 17 cells of the computing
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
theorem cell0 : cellOK 243793920 244449280 214958080 217743360 ⟨⟨65697061339, 65697061342⟩, ⟨63986434831, 67419811781⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 244449280 245104640 214958080 217743360 ⟨⟨65397149152, 65397149159⟩, ⟨63690756671, 67115621144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 243793920 244449280 217743360 220528640 ⟨⟨66514850605, 66514850606⟩, ⟨64800571755, 68241263584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244449280 245104640 217743360 220528640 ⟨⟨66211444969, 66211444975⟩, ⟨64501409903, 67933569842⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 245104640 245760000 214958080 217743360 ⟨⟨65097957511, 65097957518⟩, ⟨63395781323, 66812169041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 245760000 246415360 214958080 216350720 ⟨⟨64597555447, 64597555452⟩, ⟨63137031504, 66066613940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 245760000 246415360 216350720 217743360 ⟨⟨65001369239, 65001369246⟩, ⟨63539158585, 66472120025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 245104640 245760000 217743360 220528640 ⟨⟨65908765213, 65908765220⟩, ⟨64202956194, 67626619971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 245760000 246415360 217743360 220528640 ⟨⟨65606806183, 65606806190⟩, ⟨63905205598, 67320408692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 243793920 244449280 220528640 223313920 ⟨⟨67332012712, 67332012714⟩, ⟨65614083421, 69062086279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 244449280 245104640 220528640 223313920 ⟨⟨67025121609, 67025121616⟩, ⟨65311445796, 68750897478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 243793920 244449280 223313920 226099200 ⟨⟨68148550595, 68148550598⟩, ⟨66426972755, 69882282809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 244449280 245104640 223313920 226099200 ⟨⟨67838181963, 67838181968⟩, ⟨66120867227, 69567606950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245104640 245760000 220528640 223313920 ⟨⟨66718961642, 66718961648⟩, ⟨65009521566, 68440457803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245760000 246415360 220528640 223313920 ⟨⟨66413527628, 66413527633⟩, ⟨64708305673, 68130761949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245104640 245760000 223313920 226099200 ⟨⟨67528549640, 67528549646⟩, ⟨65815480270, 69253685393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 245760000 246415360 223313920 226099200 ⟨⟨67219648418, 67219648424⟩, ⟨65510806797, 68940512802⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 246415360 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 245104640) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 244449280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 244449280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 217743360) (by decide) (join_su (m := 245760000) (by decide) (leaf_ok cell4) (join_sr (m := 216350720) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 245760000) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_su (m := 245104640) (by decide) (join_sr (m := 223313920) (by decide) (join_su (m := 244449280) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 244449280) (by decide) (leaf_ok cell11) (leaf_ok cell12))) (join_sr (m := 223313920) (by decide) (join_su (m := 245760000) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_su (m := 245760000) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

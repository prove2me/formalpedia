-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_237240320_r148111360_153681920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:01:56.111711+00:00
-- url     : https://prove2.me/submissions/bff9cf68-b155-485d-816c-4e7fed364219

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 181/640]`, `ρ ∈ [113/640, 469/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 236257280 148111360 149504000 ⟨⟨48317778773, 48317778779⟩, ⟨47480412267, 49158259804⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 236257280 236584960 148111360 149504000 ⟨⟨48207750991, 48207750997⟩, ⟨47371439020, 49047171165⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 235929600 236257280 149504000 150896640 ⟨⟨48757830718, 48757830723⟩, ⟨47919502466, 49599274778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 236257280 236584960 149504000 150896640 ⟨⟨48646852437, 48646852442⟩, ⟨47809580185, 49487234181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 236584960 236912640 148111360 149504000 ⟨⟨48097878630, 48097878633⟩, ⟨47262618796, 48936240361⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 236912640 237240320 148111360 149504000 ⟨⟨47988161099, 47988161105⟩, ⟨47153951011, 48825466805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 236584960 236912640 149504000 150896640 ⟨⟨48536030595, 48536030597⟩, ⟨47699811942, 49375352440⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 236912640 237240320 149504000 150896640 ⟨⟨48425364598, 48425364604⟩, ⟨47590197153, 49263628962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 236257280 150896640 152289280 ⟨⟨49197676582, 49197676587⟩, ⟨48358386980, 50040083271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 236257280 236584960 150896640 152289280 ⟨⟨49085749114, 49085749121⟩, ⟨48247516972, 49927092035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 235929600 236257280 152289280 153681920 ⟨⟨49637316858, 49637316863⟩, ⟨48797066301, 50480685777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 236257280 236584960 152289280 153681920 ⟨⟨49524441512, 49524441518⟩, ⟨48685249867, 50366745216⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 236584960 236912640 150896640 152289280 ⟨⟨48973979097, 48973979100⟩, ⟨48136802011, 49814260668⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 236912640 237240320 150896640 152289280 ⟨⟨48862365932, 48862365939⟩, ⟨48026241510, 49701588572⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 236584960 236912640 152289280 153681920 ⟨⟨49411724621, 49411724622⟩, ⟨48573589485, 50252965528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 236912640 237240320 152289280 153681920 ⟨⟨49299165582, 49299165587⟩, ⟨48462084562, 50139346115⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 237240320 148111360 153681920 t = true :=
  ⟨_, (join_sr (m := 150896640) (by decide) (join_su (m := 236584960) (by decide) (join_sr (m := 149504000) (by decide) (join_su (m := 236257280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 236257280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 149504000) (by decide) (join_su (m := 236912640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 236912640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 236584960) (by decide) (join_sr (m := 152289280) (by decide) (join_su (m := 236257280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 236257280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 152289280) (by decide) (join_su (m := 236912640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 236912640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (181/640 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_226754560_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:57:10.180041+00:00
-- url     : https://prove2.me/submissions/e51d0023-d815-48dc-ba13-43180ced8bcf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 173/640]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 225771520 136970240 138362880 ⟨⟨48147025255, 48147025262⟩, ⟨47282686960, 49014683475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 225771520 226099200 136970240 138362880 ⟨⟨48039634090, 48039634096⟩, ⟨47176419817, 48906161181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 225443840 225771520 138362880 139755520 ⟨⟨48620088613, 48620088618⟩, ⟨47754736139, 49488762092⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 225771520 226099200 138362880 139755520 ⟨⟨48511700036, 48511700042⟩, ⟨47647473150, 49379240828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 226099200 226426880 136970240 138362880 ⟨⟨47932409191, 47932409197⟩, ⟨47070316237, 48797807878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 226426880 226754560 136970240 138362880 ⟨⟨47825349914, 47825349920⟩, ⟨46964375589, 48689622915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 226099200 226426880 138362880 139755520 ⟨⟨48403478916, 48403478921⟩, ⟨47540374914, 49269889748⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 226426880 226754560 138362880 139755520 ⟨⟨48295424607, 48295424612⟩, ⟨47433440797, 49160708196⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 225771520 139755520 141148160 ⟨⟨49092894922, 49092894928⟩, ⟨48226528874, 49962583051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 225771520 226099200 139755520 141148160 ⟨⟨48983510524, 48983510531⟩, ⟨48118271624, 49852064416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 225443840 225771520 141148160 142540800 ⟨⟨49565444831, 49565444837⟩, ⟨48698065810, 50436147006⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 225771520 226099200 141148160 142540800 ⟨⟨49455066201, 49455066207⟩, ⟨48588815878, 50324632593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 226099200 226426880 139755520 141148160 ⟨⟨48874294768, 48874294775⟩, ⟨48010180309, 49741717150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 226426880 226754560 139755520 141148160 ⟨⟨48765247001, 48765247007⟩, ⟨47902254289, 49631540594⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 226099200 226426880 141148160 142540800 ⟨⟨49344857386, 49344857391⟩, ⟨48479733056, 50213290725⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 226426880 226754560 141148160 142540800 ⟨⟨49234817730, 49234817736⟩, ⟨48370816697, 50102120740⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 226754560 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 226099200) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 225771520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 225771520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 226426880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 226426880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 226099200) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 225771520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 225771520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 226426880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 226426880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (173/640 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((226754560 : ℤ) : ℝ) / (D : ℝ)) = (173/640 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

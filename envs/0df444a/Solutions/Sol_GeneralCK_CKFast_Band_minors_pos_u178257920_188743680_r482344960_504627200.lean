-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_188743680_r482344960_504627200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:04:20.595524+00:00
-- url     : https://prove2.me/submissions/d2aab7e7-8ead-4ca6-bc30-683abb860015

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 9/40]`, `ρ ∈ [23/40, 77/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 180879360 482344960 487915520 ⟨⟨207542314022, 207542314031⟩, ⟨198759179327, 216509953920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178257920 180879360 487915520 493486080 ⟨⟨209646967809, 209646967817⟩, ⟨200836317570, 218641755816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 180879360 183500800 482344960 487915520 ⟨⟨204618003853, 204618003862⟩, ⟨195914629942, 213504357140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 180879360 183500800 487915520 493486080 ⟨⟨206700105038, 206700105046⟩, ⟨197969131625, 215613725973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 178257920 180879360 493486080 499056640 ⟨⟨211747505995, 211747506003⟩, ⟨202909419180, 220769357809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 178257920 180879360 499056640 504627200 ⟨⟨213843984585, 213843984593⟩, ⟨204978538927, 222892817142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 180879360 183500800 493486080 499056640 ⟨⟨208778231696, 208778231705⟩, ⟨200019734096, 217719039644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 180879360 183500800 499056640 504627200 ⟨⟨210852437432, 210852437442⟩, ⟨202066489791, 219820352924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 183500800 186122240 482344960 487915520 ⟨⟨201720703664, 201720703673⟩, ⟨193095862339, 210527016072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 183500800 186122240 487915520 493486080 ⟨⟨203780189806, 203780189814⟩, ⟨195127679078, 212613874084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 186122240 188743680 482344960 487915520 ⟨⟨198849743460, 198849743469⟩, ⟨190302236694, 207577230487⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 186122240 188743680 487915520 493486080 ⟨⟨200886556478, 200886556485⟩, ⟨192311323897, 209641504887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 183500800 186122240 493486080 499056640 ⟨⟨205835839128, 205835839138⟩, ⟨197155730694, 214696818282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 183500800 186122240 499056640 504627200 ⟨⟨207887702924, 207887702934⟩, ⟨199180067377, 216775901062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 186122240 188743680 493486080 499056640 ⟨⟨202919667052, 202919667059⟩, ⟨194316776772, 211702003465⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 186122240 188743680 499056640 504627200 ⟨⟨204949124243, 204949124253⟩, ⟨196318643347, 213758776322⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 188743680 482344960 504627200 t = true :=
  ⟨_, (join_su (m := 183500800) (by decide) (join_sr (m := 493486080) (by decide) (join_su (m := 180879360) (by decide) (join_sr (m := 487915520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 487915520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 180879360) (by decide) (join_sr (m := 499056640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 499056640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 493486080) (by decide) (join_su (m := 186122240) (by decide) (join_sr (m := 487915520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 487915520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 186122240) (by decide) (join_sr (m := 499056640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 499056640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (23/40 : ℝ) (77/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((482344960 : ℤ) : ℝ) / (D : ℝ)) = (23/40 : ℝ) := by norm_num [D]
  have e3 : (((504627200 : ℤ) : ℝ) / (D : ℝ)) = (77/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

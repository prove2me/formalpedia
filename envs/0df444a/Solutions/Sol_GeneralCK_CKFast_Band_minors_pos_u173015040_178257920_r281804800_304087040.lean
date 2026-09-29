-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u173015040_178257920_r281804800_304087040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:46:48.215345+00:00
-- url     : https://prove2.me/submissions/b4df75b1-5464-47b8-8932-12770b083864

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/160, 17/80]`, `ρ ∈ [43/128, 29/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 173015040 174325760 281804800 287375360 ⟨⟨133095245064, 133095245069⟩, ⟨128288217804, 137976540100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 174325760 175636480 281804800 287375360 ⟨⟨132063562347, 132063562356⟩, ⟨127285495296, 136915270059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 173015040 174325760 287375360 292945920 ⟨⟨135458171649, 135458171654⟩, ⟨130634072059, 140356378976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 174325760 175636480 287375360 292945920 ⟨⟨134411510533, 134411510542⟩, ⟨129616388820, 139280120848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 175636480 176947200 281804800 287375360 ⟨⟨131038962372, 131038962378⟩, ⟨126289550379, 135861396112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 176947200 178257920 281804800 287375360 ⟨⟨130021337500, 130021337507⟩, ⟨125300280432, 134814805471⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 175636480 176947200 287375360 292945920 ⟨⟨133371966932, 133371966939⟩, ⟨128605519983, 138211291342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 176947200 178257920 287375360 292945920 ⟨⟨132339433288, 132339433295⟩, ⟨127601362937, 137149777822⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 173015040 174325760 292945920 298516480 ⟨⟨137813875684, 137813875686⟩, ⟨132972804312, 142728893020⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 174325760 175636480 292945920 298516480 ⟨⟨136752377072, 136752377079⟩, ⟨131940298750, 141637790201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 173015040 174325760 298516480 304087040 ⟨⟨140162452534, 140162452540⟩, ⟨135304508269, 145094179289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 174325760 175636480 298516480 304087040 ⟨⟨139086254851, 139086254858⟩, ⟨134257316365, 143988372637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 175636480 176947200 292945920 298516480 ⟨⟨135698028444, 135698028452⟩, ⟨130914642132, 140554146194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 176947200 178257920 292945920 298516480 ⟨⟨134650722355, 134650722364⟩, ⟨129895731889, 139477848550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 175636480 176947200 298516480 304087040 ⟨⟨138017237376, 138017237385⟩, ⟨133217005741, 142890052710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 176947200 178257920 298516480 304087040 ⟨⟨136955292814, 136955292821⟩, ⟨132183473901, 141799107279⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 173015040 178257920 281804800 304087040 t = true :=
  ⟨_, (join_sr (m := 292945920) (by decide) (join_su (m := 175636480) (by decide) (join_sr (m := 287375360) (by decide) (join_su (m := 174325760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 174325760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 287375360) (by decide) (join_su (m := 176947200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 176947200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 175636480) (by decide) (join_sr (m := 298516480) (by decide) (join_su (m := 174325760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 174325760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 298516480) (by decide) (join_su (m := 176947200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 176947200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/160 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (43/128 : ℝ) (29/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  have e3 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

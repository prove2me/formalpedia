-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_188743680_r616038400_660602880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:11:14.911998+00:00
-- url     : https://prove2.me/submissions/585d9b63-3776-4ff5-92ad-957e82d5226d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 9/40]`, `ρ ∈ [47/64, 63/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 180879360 616038400 627179520 ⟨⟨258036377304, 258036377314⟩, ⟨246927610002, 269389583792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 180879360 183500800 616038400 627179520 ⟨⟨254595341753, 254595341763⟩, ⟨243591309693, 265842450058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 178257920 180879360 627179520 638320640 ⟨⟨262071158758, 262071158769⟩, ⟨250908131292, 273476887604⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 180879360 183500800 627179520 638320640 ⟨⟨258590779307, 258590779317⟩, ⟨247532096687, 269890907073⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 183500800 186122240 616038400 627179520 ⟨⟨251178985021, 251178985030⟩, ⟨240278507146, 262321161950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 186122240 188743680 616038400 627179520 ⟨⟨247786749096, 247786749106⟩, ⟨236988666701, 258825140275⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 183500800 186122240 627179520 638320640 ⟨⟨255134829850, 255134829860⟩, ⟨244179346865, 266330484414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 186122240 188743680 627179520 638320640 ⟨⟨251702761601, 251702761611⟩, ⟨240849354230, 262795050883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 178257920 180879360 638320640 649461760 ⟨⟨266094573001, 266094573011⟩, ⟨254877539960, 277552546181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 180879360 183500800 638320640 649461760 ⟨⟨262575207635, 262575207645⟩, ⟨251462119244, 273928086401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 178257920 180879360 649461760 660602880 ⟨⟨270106973033, 270106973043⟩, ⟨258836179506, 281616921867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 180879360 183500800 649461760 660602880 ⟨⟨266548966390, 266548966400⟩, ⟨255381707940, 277954336617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 183500800 186122240 638320640 649461760 ⟨⟨259080016801, 259080016811⟩, ⟨248069763574, 270328890289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 186122240 188743680 638320640 649461760 ⟨⟨255608460899, 255608460908⟩, ⟨244699953415, 266754399476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 183500800 186122240 649461760 660602880 ⟨⟨263014872564, 263014872574⟩, ⟨251950075309, 274316714775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 186122240 188743680 649461760 660602880 ⟨⟨259504161095, 259504161106⟩, ⟨248540770116, 270703508266⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 188743680 616038400 660602880 t = true :=
  ⟨_, (join_sr (m := 638320640) (by decide) (join_su (m := 183500800) (by decide) (join_sr (m := 627179520) (by decide) (join_su (m := 180879360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 180879360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 627179520) (by decide) (join_su (m := 186122240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 186122240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 183500800) (by decide) (join_sr (m := 649461760) (by decide) (join_su (m := 180879360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 180879360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 649461760) (by decide) (join_su (m := 186122240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 186122240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (47/64 : ℝ) (63/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((616038400 : ℤ) : ℝ) / (D : ℝ)) = (47/64 : ℝ) := by norm_num [D]
  have e3 : (((660602880 : ℤ) : ℝ) / (D : ℝ)) = (63/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_191365120_r170393600_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:05:00.552054+00:00
-- url     : https://prove2.me/submissions/d5d6650c-79a1-4a5c-85c4-bd4f5d8bd5d9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 73/320]`, `ρ ∈ [13/64, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 189399040 170393600 173178880 ⟨⟨75721742947, 75721742953⟩, ⟨73649134661, 77811500030⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 189399040 190054400 170393600 173178880 ⟨⟨75405312854, 75405312862⟩, ⟨73338859455, 77488832998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 188743680 189399040 173178880 175964160 ⟨⟨76883240559, 76883240565⟩, ⟨74806003249, 78977621554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 189399040 190054400 173178880 175964160 ⟨⟨76562452875, 76562452881⟩, ⟨74491381613, 78650586109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 190054400 190709760 170393600 173178880 ⟨⟨75090074820, 75090074827⟩, ⟨73029741958, 77167393000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 190709760 191365120 170393600 173178880 ⟨⟨74776019073, 74776019079⟩, ⟨72721772704, 76847169955⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 190054400 190709760 173178880 175964160 ⟨⟨76242868167, 76242868174⟩, ⟨74177928625, 78324788593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 190709760 191365120 173178880 175964160 ⟨⟨75924476604, 75924476610⟩, ⟨73865634757, 78000218862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 188743680 189399040 175964160 178749440 ⟨⟨78042896337, 78042896343⟩, ⟨75961042599, 80141888523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 189399040 190054400 175964160 178749440 ⟨⟨77717771479, 77717771485⟩, ⟨75642094751, 79810505285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 188743680 189399040 178749440 181534720 ⟨⟨79200721656, 79200721664⟩, ⟨77114263989, 81304312411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 189399040 190054400 178749440 181534720 ⟨⟨78871279873, 78871279881⟩, ⟨76791009984, 80968601826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 190054400 190709760 175964160 178749440 ⟨⟨77393860315, 77393860321⟩, ⟨75324326293, 79480370664⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 190709760 191365120 175964160 178749440 ⟨⟨77071152953, 77071152959⟩, ⟨75007727635, 79151474459⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 190054400 190709760 178749440 181534720 ⟨⟨78543062302, 78543062310⟩, ⟨76468945912, 80634150345⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 190709760 191365120 178749440 181534720 ⟨⟨78216058994, 78216059001⟩, ⟨76148062123, 80300947710⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 191365120 170393600 181534720 t = true :=
  ⟨_, (join_sr (m := 175964160) (by decide) (join_su (m := 190054400) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 189399040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 189399040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 173178880) (by decide) (join_su (m := 190709760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 190709760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 190054400) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 189399040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 189399040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178749440) (by decide) (join_su (m := 190709760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 190709760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (73/320 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((191365120 : ℤ) : ℝ) / (D : ℝ)) = (73/320 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

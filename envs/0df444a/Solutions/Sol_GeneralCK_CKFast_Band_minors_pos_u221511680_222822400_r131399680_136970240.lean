-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u221511680_222822400_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:42:51.754985+00:00
-- url     : https://prove2.me/submissions/7dea97b2-7676-48c1-b4b9-8af1fad68b8d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [169/640, 17/64]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 221511680 221839360 131399680 132792320 ⟨⟨47505637179, 47505637186⟩, ⟨46631735457, 48382942136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 221839360 222167040 131399680 132792320 ⟨⟨47400264681, 47400264683⟩, ⟨46527513806, 48276411336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 221511680 221839360 132792320 134184960 ⟨⟨47991878240, 47991878245⟩, ⟨47116940629, 48870220080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 221839360 222167040 132792320 134184960 ⟨⟨47885486891, 47885486893⟩, ⟨47011701745, 48762668821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 222167040 222494720 131399680 132792320 ⟨⟨47295061353, 47295061359⟩, ⟨46423458501, 48170052565⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 222494720 222822400 131399680 132792320 ⟨⟨47190026538, 47190026545⟩, ⟨46319568898, 48063865144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222167040 222494720 132792320 134184960 ⟨⟨47779265987, 47779265993⟩, ⟨46906630480, 48655290869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222494720 222822400 132792320 134184960 ⟨⟨47673214867, 47673214872⟩, ⟨46801726185, 48548085536⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 221511680 221839360 134184960 135577600 ⟨⟨48477839618, 48477839623⟩, ⟨47601866817, 49357217638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 221839360 222167040 134184960 135577600 ⟨⟨48370431136, 48370431139⟩, ⟨47495612409, 49248647647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 221511680 221839360 135577600 136970240 ⟨⟨48963522034, 48963522040⟩, ⟨48086514739, 49843935535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 221839360 222167040 135577600 136970240 ⟨⟨48855098131, 48855098134⟩, ⟨47979246514, 49734348530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 222167040 222494720 134184960 135577600 ⟨⟨48263194365, 48263194371⟩, ⟨47389526886, 49140252228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 222494720 222822400 134184960 135577600 ⟨⟨48156128640, 48156128645⟩, ⟨47283609591, 49032030693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 222167040 222494720 135577600 136970240 ⟨⟨48746847197, 48746847202⟩, ⟨47872148426, 49624937355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 222494720 222822400 135577600 136970240 ⟨⟨48638768560, 48638768565⟩, ⟨47765219818, 49515701318⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 221511680 222822400 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 222167040) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 221839360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 221839360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 222494720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 222494720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 222167040) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 221839360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 221839360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 222494720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 222494720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (169/640 : ℝ) (17/64 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((221511680 : ℤ) : ℝ) / (D : ℝ)) = (169/640 : ℝ) := by norm_num [D]
  have e1 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

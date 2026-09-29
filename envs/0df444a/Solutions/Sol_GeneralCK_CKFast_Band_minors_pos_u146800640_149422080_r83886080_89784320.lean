-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_149422080_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:59:36.019504+00:00
-- url     : https://prove2.me/submissions/e7421c1e-33db-48c3-8e73-702ce382052d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 57/320]`, `ρ ∈ [1/10, 137/1280]` by 19 cells of the computing
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
theorem cell0 : cellOK 146800640 147456000 83886080 85360640 ⟨⟨51071086343, 51071086350⟩, ⟨49137788191, 53021002787⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 146800640 147456000 85360640 86835200 ⟨⟨51917776319, 51917776325⟩, ⟨49981472676, 53870690416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 147456000 147783680 83886080 85360640 ⟨⟨50895530913, 50895530919⟩, ⟨49681371570, 52116297635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 147783680 148111360 83886080 85360640 ⟨⟨50778927965, 50778927973⟩, ⟨49567030634, 51997410181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 147456000 148111360 85360640 86835200 ⟨⟨51680334850, 51680334857⟩, ⟨49750545476, 53626631054⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 146800640 147456000 86835200 88309760 ⟨⟨52763119896, 52763119903⟩, ⟨50823820573, 54719021777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 146800640 147456000 88309760 89784320 ⟨⟨53607123242, 53607123248⟩, ⟨51664837986, 55566003094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 147456000 148111360 86835200 88309760 ⟨⟨52522153045, 52522153053⟩, ⟨50589378084, 54471427227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 147456000 148111360 88309760 89784320 ⟨⟨53362646844, 53362646852⟩, ⟨51426895889, 55314889344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 148111360 148439040 83886080 85360640 ⟨⟨50662670005, 50662670009⟩, ⟨49453026072, 51878876445⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 148439040 148766720 83886080 85360640 ⟨⟨50546755137, 50546755143⟩, ⟨49339356042, 51760694487⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 148111360 148766720 85360640 86835200 ⟨⟨51444294192, 51444294199⟩, ⟨49520968026, 53384024675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 148766720 149094400 83886080 85360640 ⟨⟨50431181492, 50431181499⟩, ⟨49226018728, 51642862378⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 149094400 149422080 83886080 85360640 ⟨⟨50315947206, 50315947214⟩, ⟨49113012314, 51525378209⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 148766720 149422080 85360640 86835200 ⟨⟨51209639085, 51209639089⟩, ⟨49292725673, 53142855392⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 148111360 148766720 86835200 88309760 ⟨⟨52282603870, 52282603877⟩, ⟨50356302181, 54225302545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 148111360 148766720 88309760 89784320 ⟨⟨53119604791, 53119604799⟩, ⟨51190337024, 55065262150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 148766720 149422080 86835200 88309760 ⟨⟨52044456959, 52044456964⟩, ⟨50124578063, 53980631695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 148766720 149422080 88309760 89784320 ⟨⟨52877981525, 52877981530⟩, ⟨50955146443, 54817105331⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 149422080 83886080 89784320 t = true :=
  ⟨_, (join_su (m := 148111360) (by decide) (join_sr (m := 86835200) (by decide) (join_su (m := 147456000) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 85360640) (by decide) (join_su (m := 147783680) (by decide) (leaf_ok cell2) (leaf_ok cell3)) (leaf_ok cell4))) (join_su (m := 147456000) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 88309760) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_sr (m := 86835200) (by decide) (join_su (m := 148766720) (by decide) (join_sr (m := 85360640) (by decide) (join_su (m := 148439040) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (leaf_ok cell11)) (join_sr (m := 85360640) (by decide) (join_su (m := 149094400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (leaf_ok cell14))) (join_su (m := 148766720) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_sr (m := 88309760) (by decide) (leaf_ok cell17) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (57/320 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((149422080 : ℤ) : ℝ) / (D : ℝ)) = (57/320 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

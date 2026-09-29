-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_167772160_r343408640_367001600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:03:40.194049+00:00
-- url     : https://prove2.me/submissions/67e7fb88-6116-47a3-aea8-f9ad6b0e27f5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 1/5]`, `ρ ∈ [131/320, 7/16]` by 20 cells of the computing
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
theorem cell0 : cellOK 157286400 159907840 343408640 349306880 ⟨⟨173160639508, 173160639516⟩, ⟨164278235830, 182261901320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157286400 159907840 349306880 355205120 ⟨⟨175748698844, 175748698853⟩, ⟨166834737944, 184880878383⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 159907840 162529280 343408640 349306880 ⟨⟨170603300921, 170603300929⟩, ⟨161817662566, 179604802105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 159907840 162529280 349306880 355205120 ⟨⟨173162456742, 173162456751⟩, ⟨164345163176, 182195028906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 157286400 159907840 355205120 361103360 ⟨⟨178328139488, 178328139497⟩, ⟨169382812796, 187491039032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 157286400 159907840 361103360 367001600 ⟨⟨180899091000, 180899091010⟩, ⟨171922586388, 190092516444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 159907840 162529280 355205120 361103360 ⟨⟨175713298385, 175713298394⟩, ⟨166864533061, 184776751653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 159907840 162529280 361103360 367001600 ⟨⟨178255949275, 178255949284⟩, ⟨169375892310, 187350097171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 162529280 163840000 343408640 349306880 ⟨⟨168707871818, 168707871828⟩, ⟨163367905284, 174127951776⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 163840000 165150720 343408640 349306880 ⟨⟨167454762819, 167454762828⟩, ⟨162147207931, 172841808957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 162529280 165150720 349306880 355205120 ⟨⟨170610559260, 170610559263⟩, ⟨161887918835, 179545605342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 165150720 166461440 343408640 349306880 ⟨⟨166209916981, 166209916990⟩, ⟨160934446751, 171564263407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 166461440 167772160 343408640 349306880 ⟨⟨164973212509, 164973212513⟩, ⟨159729505085, 170295188083⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 165150720 166461440 349306880 355205120 ⟨⟨168718567439, 168718567448⟩, ⟨163426078999, 174089671546⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 166461440 167772160 349306880 355205120 ⟨⟨167467453586, 167467453589⟩, ⟨162206702804, 172806222147⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 162529280 165150720 355205120 361103360 ⟨⟨173132823538, 173132823543⟩, ⟨164378625845, 182098888848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 162529280 165150720 361103360 367001600 ⟨⟨175647187122, 175647187126⟩, ⟨166861604640, 184644092725⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 165150720 166461440 355205120 361103360 ⟨⟨171219416052, 171219416061⟩, ⟨165910019094, 176607166542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 166461440 167772160 355205120 361103360 ⟨⟨169954034501, 169954034506⟩, ⟨164676347730, 175309487048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 165150720 167772160 361103360 367001600 ⟨⟨173071807881, 173071807890⟩, ⟨164378788057, 181973443406⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 167772160 343408640 367001600 t = true :=
  ⟨_, (join_su (m := 162529280) (by decide) (join_sr (m := 355205120) (by decide) (join_su (m := 159907840) (by decide) (join_sr (m := 349306880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 349306880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 159907840) (by decide) (join_sr (m := 361103360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 361103360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 355205120) (by decide) (join_su (m := 165150720) (by decide) (join_sr (m := 349306880) (by decide) (join_su (m := 163840000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 349306880) (by decide) (join_su (m := 166461440) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 166461440) (by decide) (leaf_ok cell13) (leaf_ok cell14)))) (join_su (m := 165150720) (by decide) (join_sr (m := 361103360) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_sr (m := 361103360) (by decide) (join_su (m := 166461440) (by decide) (leaf_ok cell17) (leaf_ok cell18)) (leaf_ok cell19)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (131/320 : ℝ) (7/16 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((343408640 : ℤ) : ℝ) / (D : ℝ)) = (131/320 : ℝ) := by norm_num [D]
  have e3 : (((367001600 : ℤ) : ℝ) / (D : ℝ)) = (7/16 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

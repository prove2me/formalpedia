-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_167772160_r319815680_343408640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:03:38.109977+00:00
-- url     : https://prove2.me/submissions/5a27224f-bcdf-4a6c-9bea-d34841bbafb9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 1/5]`, `ρ ∈ [61/160, 131/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 162529280 163840000 319815680 325713920 ⟨⟨158474524097, 158474524104⟩, ⟨153203580089, 163826692199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 163840000 165150720 319815680 325713920 ⟨⟨157280645821, 157280645828⟩, ⟨152042214548, 162599636000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 162529280 163840000 325713920 331612160 ⟨⟨161045613342, 161045613350⟩, ⟨155757230737, 166414944778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163840000 165150720 325713920 331612160 ⟨⟨159836693589, 159836693598⟩, ⟨154580802355, 165172879274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 165150720 166461440 319815680 325713920 ⟨⟨156094971953, 156094971961⟩, ⟨150888713676, 161381132119⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 166461440 167772160 319815680 325713920 ⟨⟨154917378650, 154917378653⟩, ⟨149742959145, 160171051062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 165150720 166461440 325713920 331612160 ⟨⟨158635996416, 158635996423⟩, ⟨153412259962, 163939380841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 166461440 167772160 325713920 331612160 ⟨⟨157443398445, 157443398449⟩, ⟨152251485604, 162714320554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 162529280 163840000 331612160 337510400 ⟨⟨163608117181, 163608117189⟩, ⟨158302419516, 168994486796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 163840000 165150720 331612160 337510400 ⟨⟨162384313885, 162384313894⟩, ⟨157111083572, 167737572539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 162529280 163840000 337510400 343408640 ⟨⟨166162161877, 166162161886⟩, ⟨160839270338, 171565446890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 163840000 165150720 337510400 343408640 ⟨⟨164923629851, 164923629858⟩, ⟨159633179062, 170293841238⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 165150720 166461440 331612160 337510400 ⟨⟨161168748967, 161168748977⟩, ⟨155927652593, 166489237712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 166461440 167772160 331612160 337510400 ⟨⟨159961299553, 159961299557⟩, ⟨154752009029, 165249353991⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 165150720 166461440 337510400 343408640 ⟨⟨163693349705, 163693349714⟩, ⟨158435009458, 169030825057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 166461440 167772160 337510400 343408640 ⟨⟨162471199095, 162471199099⟩, ⟨157244644408, 167776270652⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 167772160 319815680 343408640 t = true :=
  ⟨_, (join_sr (m := 331612160) (by decide) (join_su (m := 165150720) (by decide) (join_sr (m := 325713920) (by decide) (join_su (m := 163840000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 163840000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 325713920) (by decide) (join_su (m := 166461440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 166461440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 165150720) (by decide) (join_sr (m := 337510400) (by decide) (join_su (m := 163840000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 163840000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 337510400) (by decide) (join_su (m := 166461440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 166461440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (61/160 : ℝ) (131/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  have e3 : (((343408640 : ℤ) : ℝ) / (D : ℝ)) = (131/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

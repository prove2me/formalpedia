-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u75497472_79691776_r123535360_135659520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:46:51.817175+00:00
-- url     : https://prove2.me/submissions/35f4e53c-d4c7-4b12-bf01-bbef22deef00

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/100, 19/200]`, `ρ ∈ [377/2560, 207/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 75497472 76546048 123535360 126566400 ⟨⟨126287336164, 126287336176⟩, ⟨120635918558, 132053337869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 75497472 76546048 126566400 129597440 ⟨⟨128848895447, 128848895459⟩, ⟨123188974402, 134622571299⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 76546048 77594624 123535360 126566400 ⟨⟨125118059921, 125118059933⟩, ⟨119521870217, 130826922424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 76546048 77594624 126566400 129597440 ⟨⟨127662976312, 127662976322⟩, ⟨122058128312, 133379698177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 75497472 76546048 129597440 132628480 ⟨⟨131392684356, 131392684368⟩, ⟨125724524554, 137173775327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 75497472 76546048 132628480 135659520 ⟨⟨133919003839, 133919003851⟩, ⟨128242862006, 139707258869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 76546048 77594624 129597440 132628480 ⟨⟨130190473085, 130190473095⟩, ⟨124577226432, 135914799914⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 76546048 77594624 132628480 135659520 ⟨⟨132700841995, 132700842005⟩, ⟨127079448654, 138432527082⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 77594624 78643200 123535360 126566400 ⟨⟨123967575122, 123967575134⟩, ⟨118425470804, 129620492001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 77594624 78643200 126566400 129597440 ⟨⟨126495964987, 126495964997⟩, ⟨120945057576, 132156915139⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 78643200 79691776 123535360 126566400 ⟨⟨122835378526, 122835378536⟩, ⟨117346252383, 128433506209⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 78643200 79691776 126566400 129597440 ⟨⟨125347358522, 125347358534⟩, ⟨119849294018, 130953682673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 77594624 78643200 129597440 132628480 ⟨⟨129007278154, 129007278166⟩, ⟨123447822300, 134676011784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 77594624 78643200 132628480 135659520 ⟨⟨131501797500, 131501797510⟩, ⟨125934040454, 137178072239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 78643200 79691776 129597440 132628480 ⟨⟨127842597104, 127842597116⟩, ⟨122335843953, 133456872503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 78643200 79691776 132628480 135659520 ⟨⟨130321368575, 130321368585⟩, ⟨124806169347, 135943357170⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 75497472 79691776 123535360 135659520 t = true :=
  ⟨_, (join_su (m := 77594624) (by decide) (join_sr (m := 129597440) (by decide) (join_su (m := 76546048) (by decide) (join_sr (m := 126566400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 126566400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 76546048) (by decide) (join_sr (m := 132628480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 132628480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 129597440) (by decide) (join_su (m := 78643200) (by decide) (join_sr (m := 126566400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 126566400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 78643200) (by decide) (join_sr (m := 132628480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 132628480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (19/200 : ℝ) →
    rho ∈ Set.Icc (377/2560 : ℝ) (207/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e1 : (((79691776 : ℤ) : ℝ) / (D : ℝ)) = (19/200 : ℝ) := by norm_num [D]
  have e2 : (((123535360 : ℤ) : ℝ) / (D : ℝ)) = (377/2560 : ℝ) := by norm_num [D]
  have e3 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u212336640_214958080_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:13:40.688114+00:00
-- url     : https://prove2.me/submissions/170b6d9c-c99c-4825-a2af-655c001c7f34

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [81/320, 41/160]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 212336640 212992000 136970240 138362880 ⟨⟨52529445910, 52529445916⟩, ⟨51006185827, 54062568194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 212336640 212992000 138362880 139755520 ⟨⟨53042904184, 53042904190⟩, ⟨51517683623, 54577991298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212992000 213647360 136970240 138362880 ⟨⟨52300625190, 52300625197⟩, ⟨50780874063, 53830200023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212992000 213647360 138362880 139755520 ⟨⟨52811989416, 52811989422⟩, ⟨51290283192, 54343523751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 212336640 212992000 139755520 141148160 ⟨⟨53556035387, 53556035392⟩, ⟨52028855645, 55093086018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 212336640 212992000 141148160 142540800 ⟨⟨54068840404, 54068840409⟩, ⟨52539702773, 55607853242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212992000 213647360 139755520 141148160 ⟨⟨53323030475, 53323030481⟩, ⟨51799370420, 54856523024⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 212992000 213647360 141148160 142540800 ⟨⟨53833749237, 53833749243⟩, ⟨52308136618, 55369198719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 213647360 214302720 136970240 138362880 ⟨⟨52072578181, 52072578186⟩, ⟨50556317002, 53598624853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 213647360 214302720 138362880 139755520 ⟨⟨52581853759, 52581853764⟩, ⟨51063642851, 54109854613⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 214302720 214958080 136970240 138362880 ⟨⟨51845298743, 51845298747⟩, ⟨50332508657, 53367836386⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 214302720 214958080 138362880 139755520 ⟨⟨52352491040, 52352491041⟩, ⟨50837756582, 53876977554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 213647360 214302720 139755520 141148160 ⟨⟨53090810032, 53090810039⟩, ⟨51570650637, 54620763810⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 213647360 214302720 141148160 142540800 ⟨⟨53599447859, 53599447865⟩, ⟨52077341212, 55131353305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 214302720 214958080 139755520 141148160 ⟨⟨52859367851, 52859367856⟩, ⟨51342690238, 54385802009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 214302720 214958080 141148160 142540800 ⟨⟨53365930027, 53365930031⟩, ⟨51847310467, 54894310597⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 212336640 214958080 136970240 142540800 t = true :=
  ⟨_, (join_su (m := 213647360) (by decide) (join_sr (m := 139755520) (by decide) (join_su (m := 212992000) (by decide) (join_sr (m := 138362880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 138362880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 212992000) (by decide) (join_sr (m := 141148160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 141148160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 139755520) (by decide) (join_su (m := 214302720) (by decide) (join_sr (m := 138362880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 138362880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 214302720) (by decide) (join_sr (m := 141148160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 141148160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (81/320 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

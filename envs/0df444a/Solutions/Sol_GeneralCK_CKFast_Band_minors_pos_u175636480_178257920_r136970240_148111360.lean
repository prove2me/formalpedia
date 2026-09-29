-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u175636480_178257920_r136970240_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:14:42.896245+00:00
-- url     : https://prove2.me/submissions/a20ff88d-cdeb-4a9d-b3e0-f72185abc46d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [67/320, 17/80]`, `ρ ∈ [209/1280, 113/640]` by 19 cells of the computing
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
theorem cell0 : cellOK 175636480 176291840 136970240 139755520 ⟨⟨67119371778, 67119371786⟩, ⟨64975491229, 69282332163⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 176291840 176947200 136970240 138362880 ⟨⟨66514864526, 66514864532⟩, ⟨64763936830, 68278303447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 176291840 176947200 138362880 139755520 ⟨⟨67152945013, 67152945019⟩, ⟨65399747720, 68918653349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 175636480 176291840 139755520 142540800 ⟨⟨68399203073, 68399203079⟩, ⟨66250259551, 70567214988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 176291840 176947200 139755520 142540800 ⟨⟨68108906573, 68108906580⟩, ⟨65966741910, 70270038400⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 176947200 177602560 136970240 138362880 ⟨⟨66231945966, 66231945973⟩, ⟨64485873699, 67990469953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 176947200 177602560 138362880 139755520 ⟨⟨66867573774, 66867573780⟩, ⟨65119237669, 68628361538⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 177602560 178257920 136970240 138362880 ⟨⟨65950256239, 65950256247⟩, ⟨64209008346, 67703896852⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 177602560 178257920 138362880 139755520 ⟨⟨66583439113, 66583439119⟩, ⟨64839933145, 68339337865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 176947200 177602560 139755520 142540800 ⟨⟨67819869312, 67819869320⟩, ⟨65684441934, 69974163483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 177602560 178257920 139755520 142540800 ⟨⟨67532080116, 67532080123⟩, ⟨65403348854, 69679578652⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 175636480 176291840 142540800 145326080 ⟨⟨69676544737, 69676544744⟩, ⟨67522557188, 71849589087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 176291840 176947200 142540800 145326080 ⟨⟨69381369149, 69381369155⟩, ⟨67234173907, 71547520418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 175636480 176291840 145326080 148111360 ⟨⟨70951413615, 70951413622⟩, ⟨68792400815, 73129471468⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 176291840 176947200 145326080 148111360 ⟨⟨70651386531, 70651386537⟩, ⟨68499179203, 72822538598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 176947200 177602560 142540800 145326080 ⟨⟨69087467957, 69087467964⟩, ⟨66947023462, 71246768561⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 177602560 178257920 142540800 145326080 ⟨⟨68794829890, 68794829897⟩, ⟨66661094983, 70947321831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 176947200 177602560 145326080 148111360 ⟨⟨70352648713, 70352648721⟩, ⟨68207205313, 72516937389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 177602560 178257920 145326080 148111360 ⟨⟨70055188797, 70055188803⟩, ⟨67916468177, 72212656061⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 175636480 178257920 136970240 148111360 t = true :=
  ⟨_, (join_sr (m := 142540800) (by decide) (join_su (m := 176947200) (by decide) (join_sr (m := 139755520) (by decide) (join_su (m := 176291840) (by decide) (leaf_ok cell0) (join_sr (m := 138362880) (by decide) (leaf_ok cell1) (leaf_ok cell2))) (join_su (m := 176291840) (by decide) (leaf_ok cell3) (leaf_ok cell4))) (join_sr (m := 139755520) (by decide) (join_su (m := 177602560) (by decide) (join_sr (m := 138362880) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 138362880) (by decide) (leaf_ok cell7) (leaf_ok cell8))) (join_su (m := 177602560) (by decide) (leaf_ok cell9) (leaf_ok cell10)))) (join_su (m := 176947200) (by decide) (join_sr (m := 145326080) (by decide) (join_su (m := 176291840) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 176291840) (by decide) (leaf_ok cell13) (leaf_ok cell14))) (join_sr (m := 145326080) (by decide) (join_su (m := 177602560) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_su (m := 177602560) (by decide) (leaf_ok cell17) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (67/320 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((175636480 : ℤ) : ℝ) / (D : ℝ)) = (67/320 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

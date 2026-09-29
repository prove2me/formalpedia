-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u231997440_233308160_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:23:22.214988+00:00
-- url     : https://prove2.me/submissions/19547b23-eb5a-44db-acb4-44447bf9b55a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [177/640, 89/320]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 231997440 232325120 136970240 138362880 ⟨⟨46030072709, 46030072714⟩, ⟨45187713626, 46875614106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 232325120 232652800 136970240 138362880 ⟨⟨45925887821, 45925887827⟩, ⟨45084600714, 46770350606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231997440 232325120 138362880 139755520 ⟨⟨46483409862, 46483409868⟩, ⟨45640067586, 47329935686⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 232325120 232652800 138362880 139755520 ⟨⟨46378250673, 46378250678⟩, ⟨45535981902, 47223696361⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 232652800 232980480 136970240 138362880 ⟨⟨45821856860, 45821856867⟩, ⟨44981639229, 46665243555⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 232980480 233308160 136970240 138362880 ⟨⟨45717979238, 45717979243⟩, ⟨44878828593, 46560292353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 232652800 232980480 138362880 139755520 ⟨⟨46273246526, 46273246531⟩, ⟨45432048760, 47117614602⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 232980480 233308160 138362880 139755520 ⟨⟨46168396831, 46168396836⟩, ⟨45328267577, 47011689808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 231997440 232325120 139755520 141148160 ⟨⟨46936520262, 46936520267⟩, ⟨46092195265, 47784030034⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 232325120 232652800 139755520 141148160 ⟨⟨46830388202, 46830388207⟩, ⟨45987138235, 47676816322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 231997440 232325120 141148160 142540800 ⟨⟨47389404459, 47389404465⟩, ⟨46544097216, 48237897703⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 232325120 232652800 141148160 142540800 ⟨⟨47282300957, 47282300963⟩, ⟨46438070262, 48129711038⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 232652800 232980480 139755520 141148160 ⟨⟨46724412295, 46724412300⟩, ⟨45882234855, 47569761287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 232980480 233308160 139755520 141148160 ⟨⟨46618591944, 46618591949⟩, ⟨45777484538, 47462864323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 232652800 232980480 141148160 142540800 ⟨⟨47175354710, 47175354715⟩, ⟨46332198057, 48021684152⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 232980480 233308160 141148160 142540800 ⟨⟨47068565116, 47068565121⟩, ⟨46226480013, 47913816439⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 231997440 233308160 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 232652800) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 232325120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 232325120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 232980480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 232980480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 232652800) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 232325120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 232325120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 232980480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 232980480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (177/640 : ℝ) (89/320 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((231997440 : ℤ) : ℝ) / (D : ℝ)) = (177/640 : ℝ) := by norm_num [D]
  have e1 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

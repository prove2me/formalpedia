-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u237240320_238551040_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:39:59.31955+00:00
-- url     : https://prove2.me/submissions/7a8805c2-c6af-4cb5-986d-c5a9cfabfd90

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [181/640, 91/320]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 237240320 237568000 136970240 138362880 ⟨⟨44381260519, 44381260525⟩, ⟨43555758572, 45209841228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 237568000 237895680 136970240 138362880 ⟨⟨44279469197, 44279469202⟩, ⟨43455000383, 45107010481⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 237240320 237568000 138362880 139755520 ⟨⟨44819140824, 44819140829⟩, ⟨43992679947, 45648681798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237568000 237895680 138362880 139755520 ⟨⟨44716392636, 44716392642⟩, ⟨43890966396, 45544892692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 237895680 238223360 136970240 138362880 ⟨⟨44177822677, 44177822682⟩, ⟨43354384646, 45004326911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 238223360 238551040 136970240 138362880 ⟨⟨44076320411, 44076320414⟩, ⟨43253910823, 44901789952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237895680 238223360 138362880 139755520 ⟨⟨44613790313, 44613790318⟩, ⟨43789396354, 45441251824⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 238223360 238551040 138362880 139755520 ⟨⟨44511333301, 44511333302⟩, ⟨43687969281, 45337758626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 237240320 237568000 139755520 141148160 ⟨⟨45256816407, 45256816412⟩, ⟨44429396985, 46087317260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 237568000 237895680 139755520 141148160 ⟨⟨45153112672, 45153112677⟩, ⟨44326729380, 45982571116⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 237240320 237568000 141148160 142540800 ⟨⟨45694287752, 45694287758⟩, ⟨44865910166, 46525748100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 237568000 237895680 141148160 142540800 ⟨⟨45589629781, 45589629787⟩, ⟨44762289816, 46420046235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 237895680 238223360 139755520 141148160 ⟨⟨45049555853, 45049555858⟩, ⟨44224206337, 45877974264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 238223360 238551040 139755520 141148160 ⟨⟨44946145395, 44946145397⟩, ⟨44121827311, 45773526135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 237895680 238223360 141148160 142540800 ⟨⟨45485119771, 45485119778⟩, ⟨44658815071, 46314494712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 238223360 238551040 141148160 142540800 ⟨⟨45380757167, 45380757170⟩, ⟨44555485384, 46209092954⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 237240320 238551040 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 237895680) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 237568000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 237568000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 238223360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 238223360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 237895680) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 237568000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 237568000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 238223360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 238223360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (181/640 : ℝ) (91/320 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e1 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

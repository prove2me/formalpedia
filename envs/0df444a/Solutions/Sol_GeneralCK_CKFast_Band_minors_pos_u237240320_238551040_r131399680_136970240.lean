-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u237240320_238551040_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:35:21.653221+00:00
-- url     : https://prove2.me/submissions/6260f587-309f-4775-aa9a-0a01794073d9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [181/640, 91/320]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 237240320 237568000 131399680 132792320 ⟨⟨42627682358, 42627682364⟩, ⟨41806019969, 43452418128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 237568000 237895680 131399680 132792320 ⟨⟨42529731730, 42529731736⟩, ⟨41709096417, 43353434110⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 237240320 237568000 132792320 134184960 ⟨⟨43066386415, 43066386421⟩, ⟨42243763559, 43892084004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237568000 237895680 132792320 134184960 ⟨⟨42967473620, 42967473625⟩, ⟨42145879361, 43792136302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 237895680 238223360 131399680 132792320 ⟨⟨42431921593, 42431921600⟩, ⟨41612311013, 43254592949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 238223360 238551040 131399680 132792320 ⟨⟨42334251416, 42334251417⟩, ⟨41515663234, 43155894096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237895680 238223360 132792320 134184960 ⟨⟨42868702405, 42868702410⟩, ⟨42048134399, 43692332548⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 238223360 238551040 132792320 134184960 ⟨⟨42770072233, 42770072235⟩, ⟨41950528145, 43592672187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 237240320 237568000 134184960 135577600 ⟨⟨43504883803, 43504883808⟩, ⟨42681300863, 44331542820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 237568000 237895680 134184960 135577600 ⟨⟨43405010171, 43405010177⟩, ⟨42582457347, 44230632770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 237240320 237568000 135577600 136970240 ⟨⟨43943175008, 43943175013⟩, ⟨43118632373, 44770795065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 237568000 237895680 135577600 136970240 ⟨⟨43842341869, 43842341874⟩, ⟨43018830861, 44668924003⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 237895680 238223360 134184960 135577600 ⟨⟨43305279202, 43305279207⟩, ⟨42483754147, 44129867752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 238223360 238551040 134184960 135577600 ⟨⟨43205690353, 43205690356⟩, ⟨42385190729, 44029247209⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 237895680 238223360 135577600 136970240 ⟨⟨43741652466, 43741652471⟩, ⟨42919170736, 44567199047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 238223360 238551040 135577600 136970240 ⟨⟨43641106254, 43641106257⟩, ⟨42819651464, 44465619638⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 237240320 238551040 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 237895680) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 237568000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 237568000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 238223360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 238223360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 237895680) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 237568000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 237568000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 238223360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 238223360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (181/640 : ℝ) (91/320 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e1 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

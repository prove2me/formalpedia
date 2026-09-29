-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u175636480_178257920_r159252480_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:14:59.147797+00:00
-- url     : https://prove2.me/submissions/b8c01537-f1fa-4c6a-a23e-882708350e80

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [67/320, 17/80]`, `ρ ∈ [243/1280, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 175636480 176291840 159252480 162037760 ⟨⟨77289246488, 77289246496⟩, ⟨75105383497, 79492093548⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 176291840 176947200 159252480 162037760 ⟨⟨76965366951, 76965366959⟩, ⟨74788371096, 79161248877⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 175636480 176291840 162037760 164823040 ⟨⟨78549625017, 78549625024⟩, ⟨76360846097, 80757375366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 176291840 176947200 162037760 164823040 ⟨⟨78221054257, 78221054263⟩, ⟨76039153997, 80421828413⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 176947200 177602560 159252480 162037760 ⟨⟨76642846847, 76642846855⟩, ⟨74472676708, 78831805868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 177602560 178257920 159252480 162037760 ⟨⟨76321674381, 76321674387⟩, ⟨74158288930, 78503752320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 176947200 177602560 162037760 164823040 ⟨⟨77893856154, 77893856160⟩, ⟨75718793168, 80087696303⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 177602560 178257920 162037760 164823040 ⟨⟨77568018831, 77568018837⟩, ⟨75399752126, 79754966759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 175636480 176291840 164823040 167608320 ⟨⟨79807645027, 79807645035⟩, ⟨77613967856, 82020280845⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 176291840 176947200 164823040 167608320 ⟨⟨79474408900, 79474408907⟩, ⟨77287621650, 81680057728⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 175636480 176291840 167608320 170393600 ⟨⟨81063322343, 81063322350⟩, ⟨78864764447, 83280825958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 176291840 176947200 167608320 170393600 ⟨⟨80725446467, 80725446473⟩, ⟨78533789495, 82935952556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 176947200 177602560 164823040 167608320 ⟨⟨79142558389, 79142558397⟩, ⟨76962619714, 81341262370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 177602560 178257920 164823040 167608320 ⟨⟨78812081547, 78812081555⟩, ⟨76638950488, 81003882423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 176947200 177602560 167608320 170393600 ⟨⟨80388968910, 80388968917⟩, ⟨78204171555, 82592519567⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 177602560 178257920 167608320 170393600 ⟨⟨80053877653, 80053877659⟩, ⟨77875898999, 82250514573⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 175636480 178257920 159252480 170393600 t = true :=
  ⟨_, (join_sr (m := 164823040) (by decide) (join_su (m := 176947200) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 176291840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 176291840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 162037760) (by decide) (join_su (m := 177602560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 177602560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 176947200) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 176291840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 176291840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 167608320) (by decide) (join_su (m := 177602560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 177602560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (67/320 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((175636480 : ℤ) : ℝ) / (D : ℝ)) = (67/320 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

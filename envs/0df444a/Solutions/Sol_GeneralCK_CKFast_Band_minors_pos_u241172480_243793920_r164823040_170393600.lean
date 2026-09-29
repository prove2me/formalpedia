-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_243793920_r164823040_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T10:57:58.967604+00:00
-- url     : https://prove2.me/submissions/7a20467f-bcbb-46f5-bae3-5a96dad703a5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 93/320]`, `ρ ∈ [503/2560, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 241827840 164823040 166215680 ⟨⟨51603665443, 51603665448⟩, ⟨50184044359, 53031805376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241172480 241827840 166215680 167608320 ⟨⟨52025967078, 52025967085⟩, ⟨50604618746, 53455839984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241827840 242483200 164823040 166215680 ⟨⟨51366487660, 51366487666⟩, ⟨49949760912, 52791705429⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 241827840 242483200 166215680 167608320 ⟨⟨51786950375, 51786950382⟩, ⟨50368500960, 53213896561⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241172480 241827840 167608320 169000960 ⟨⟨52448088532, 52448088538⟩, ⟨51025013300, 53879694051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 241172480 241827840 169000960 170393600 ⟨⟨52870030224, 52870030230⟩, ⟨51445228439, 54303367998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 241827840 242483200 167608320 169000960 ⟨⟨52207235225, 52207235231⟩, ⟨50787063476, 53635909484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 241827840 242483200 169000960 170393600 ⟨⟨52627342622, 52627342628⟩, ⟨51205448873, 54057744611⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 242483200 243138560 164823040 166215680 ⟨⟨51129936491, 51129936496⟩, ⟨49716090357, 52552245992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 242483200 243138560 166215680 167608320 ⟨⟨51548563839, 51548563845⟩, ⟨50132999614, 52972597209⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243138560 243793920 164823040 166215680 ⟨⟨50894007305, 50894007312⟩, ⟨49483028169, 52313422337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 243138560 243793920 166215680 167608320 ⟨⟨51310802821, 51310802828⟩, ⟨49898110160, 52731937179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 242483200 243138560 167608320 169000960 ⟨⟨51967015615, 51967015621⟩, ⟨50549733617, 53392772523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 242483200 243138560 169000960 170393600 ⟨⟨52385292224, 52385292231⟩, ⟨50966292772, 53812772343⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 243138560 243793920 167608320 169000960 ⟨⟨51727425032, 51727425039⟩, ⟨50313019152, 53150278401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 243138560 243793920 169000960 170393600 ⟨⟨52143874341, 52143874346⟩, ⟨50727755544, 53568446406⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 243793920 164823040 170393600 t = true :=
  ⟨_, (join_su (m := 242483200) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 241827840) (by decide) (join_sr (m := 166215680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 166215680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 241827840) (by decide) (join_sr (m := 169000960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 169000960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 167608320) (by decide) (join_su (m := 243138560) (by decide) (join_sr (m := 166215680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 166215680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 243138560) (by decide) (join_sr (m := 169000960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 169000960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (503/2560 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

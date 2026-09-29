-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u75497472_83886080_r208404480_232652800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:52:09.866964+00:00
-- url     : https://prove2.me/submissions/e9d7f0da-1ac8-45e3-ab77-1622fd369482

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/100, 1/10]`, `ρ ∈ [159/640, 71/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 75497472 77594624 208404480 214466560 ⟨⟨192467687721, 192467687732⟩, ⟨180984141989, 204321343967⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 75497472 77594624 214466560 220528640 ⟨⟨196752875414, 196752875424⟩, ⟨185254478507, 208616098339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 77594624 79691776 208404480 214466560 ⟨⟨189442208576, 189442208582⟩, ⟨178151223698, 201093961122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 77594624 79691776 214466560 220528640 ⟨⟨193689893922, 193689893925⟩, ⟨182382422504, 205353161081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 75497472 77594624 220528640 226590720 ⟨⟨200993744635, 200993744648⟩, ⟨189481405821, 212865702672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 75497472 77594624 226590720 232652800 ⟨⟨205191557323, 205191557336⟩, ⟨193666137030, 217071466486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 77594624 79691776 220528640 226590720 ⟨⟨197894594926, 197894594932⟩, ⟨186571535793, 209568547001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 77594624 79691776 226590720 232652800 ⟨⟨202057514166, 202057514174⟩, ⟨190719719547, 213741367046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 79691776 81788928 208404480 214466560 ⟨⟨186493661915, 186493661927⟩, ⟨175388718130, 197950403295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 79691776 81788928 214466560 220528640 ⟨⟨190703724818, 190703724828⟩, ⟨179580792118, 202173775854⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 81788928 83886080 208404480 214466560 ⟨⟨183618680546, 183618680559⟩, ⟨172693586356, 194886955448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 81788928 83886080 214466560 220528640 ⟨⟨187791041658, 187791041668⟩, ⟨176846578899, 199074280104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 79691776 81788928 220528640 226590720 ⟨⟨194872100678, 194872100691⟩, ⟨183732065515, 206354636317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 79691776 81788928 226590720 232652800 ⟨⟨198999935616, 198999935629⟩, ⟨187843640034, 210494174413⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 81788928 83886080 220528640 226590720 ⟨⟨191922976775, 191922976785⟩, ⟨180960017912, 203220360731⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 81788928 83886080 226590720 232652800 ⟨⟨196015578312, 196015578325⟩, ⟨185034953528, 207326331420⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 75497472 83886080 208404480 232652800 t = true :=
  ⟨_, (join_su (m := 79691776) (by decide) (join_sr (m := 220528640) (by decide) (join_su (m := 77594624) (by decide) (join_sr (m := 214466560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 214466560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 77594624) (by decide) (join_sr (m := 226590720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 226590720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 220528640) (by decide) (join_su (m := 81788928) (by decide) (join_sr (m := 214466560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 214466560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 81788928) (by decide) (join_sr (m := 226590720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 226590720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (159/640 : ℝ) (71/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  have e3 : (((232652800 : ℤ) : ℝ) / (D : ℝ)) = (71/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

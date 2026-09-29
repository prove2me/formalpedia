-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u228065280_230686720_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:04:16.446663+00:00
-- url     : https://prove2.me/submissions/8bd83379-ca58-4c62-a0e8-b77bcb462569

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [87/320, 11/40]`, `ρ ∈ [311/1280, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 228065280 228720640 203816960 206602240 ⟨⟨69503392287, 69503392293⟩, ⟨67701073481, 71318955255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 228720640 229376000 203816960 206602240 ⟨⟨69199165981, 69199165986⟩, ⟨67401506899, 71010017312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 228065280 228720640 206602240 209387520 ⟨⟨70410120820, 70410120825⟩, ⟨68603900434, 72229592877⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 228720640 229376000 206602240 209387520 ⟨⟨70102223213, 70102223219⟩, ⟨68300672633, 71916973698⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 229376000 230031360 203816960 206602240 ⟨⟨68895770657, 68895770662⟩, ⟨67102750246, 70701931733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230031360 230686720 203816960 206602240 ⟨⟨68593200270, 68593200276⟩, ⟨66804797630, 70394692311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 229376000 230031360 206602240 209387520 ⟨⟨69795163028, 69795163034⟩, ⟨67998261200, 71605213317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 230031360 230686720 206602240 209387520 ⟨⟨69488934184, 69488934191⟩, ⟨67696660210, 71294305496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 228065280 228720640 209387520 212172800 ⟨⟨71315987574, 71315987579⟩, ⟨69505869398, 73139364865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 228720640 229376000 209387520 212172800 ⟨⟨71004429049, 71004429054⟩, ⟨69198990671, 72823074920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 228720640 212172800 214958080 ⟨⟨72220996867, 72220996874⟩, ⟨70406984668, 74048275558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228720640 229376000 212172800 214958080 ⟨⟨71905787741, 71905787747⟩, ⟨70096465243, 73728325254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 229376000 230031360 209387520 212172800 ⟨⟨70693714283, 70693714290⟩, ⟨68892934650, 72507650105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 230031360 230686720 209387520 212172800 ⟨⟨70383837163, 70383837170⟩, ⟨68587695379, 72193084152⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 229376000 230031360 212172800 214958080 ⟨⟨71591428610, 71591428617⟩, ⟨69786774764, 73409246309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 230031360 230686720 212172800 214958080 ⟨⟨71277913330, 71277913336⟩, ⟨69477907241, 73091032427⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 228065280 230686720 203816960 214958080 t = true :=
  ⟨_, (join_sr (m := 209387520) (by decide) (join_su (m := 229376000) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 228720640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 228720640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 206602240) (by decide) (join_su (m := 230031360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 230031360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 229376000) (by decide) (join_sr (m := 212172800) (by decide) (join_su (m := 228720640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 228720640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 212172800) (by decide) (join_su (m := 230031360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 230031360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (87/320 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

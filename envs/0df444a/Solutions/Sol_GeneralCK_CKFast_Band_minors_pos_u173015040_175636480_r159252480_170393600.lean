-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u173015040_175636480_r159252480_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:14:59.437731+00:00
-- url     : https://prove2.me/submissions/3b5423dd-15d1-47cb-84c1-29f290d026a1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/160, 67/320]`, `ρ ∈ [243/1280, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 173015040 173670400 159252480 162037760 ⟨⟨78598599603, 78598599610⟩, ⟨76386845818, 80829737724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 173670400 174325760 159252480 162037760 ⟨⟨78269161676, 78269161683⟩, ⟨76064444745, 80493161617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 173015040 173670400 162037760 164823040 ⟨⟨79877876804, 79877876810⟩, ⟨77661161374, 82113961995⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 173670400 174325760 162037760 164823040 ⟨⟨79543693986, 79543693992⟩, ⟨77334026778, 81772630122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 174325760 174981120 159252480 162037760 ⟨⟨77941131718, 77941131726⟩, ⟨75743408594, 80158037370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 174981120 175636480 159252480 162037760 ⟨⟨77614497390, 77614497394⟩, ⟨75423725443, 79824352220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 174325760 174981120 162037760 164823040 ⟨⟨79210932671, 79210932677⟩, ⟨77008270682, 81432763596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 174981120 175636480 162037760 164823040 ⟨⟨78879580443, 78879580445⟩, ⟨76683881079, 81094349576⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 173015040 173670400 164823040 167608320 ⟨⟨81154689392, 81154689399⟩, ⟨78933031073, 83395702750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 173670400 174325760 164823040 167608320 ⟨⟨80815788612, 80815788619⟩, ⟨78601189610, 83049642317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 173015040 173670400 167608320 170393600 ⟨⟨82429054178, 82429054184⟩, ⟨80202471561, 84674976962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 173670400 174325760 167608320 170393600 ⟨⟨82085462114, 82085462120⟩, ⟨79865949639, 84324214919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 174325760 174981120 164823040 167608320 ⟨⟨80478322597, 80478322604⟩, ⟨78270739953, 82705060440⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 174981120 175636480 164823040 167608320 ⟨⟨80142278856, 80142278859⟩, ⟨77941670018, 82361944206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 174325760 174981120 167608320 170393600 ⟨⟨81743317808, 81743317814⟩, ⟨79530832561, 83974944371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 174981120 175636480 167608320 170393600 ⟨⟨81402608695, 81402608698⟩, ⟨79197108171, 83627152331⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 173015040 175636480 159252480 170393600 t = true :=
  ⟨_, (join_sr (m := 164823040) (by decide) (join_su (m := 174325760) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 173670400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 173670400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 162037760) (by decide) (join_su (m := 174981120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 174981120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 174325760) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 173670400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 173670400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 167608320) (by decide) (join_su (m := 174981120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 174981120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/160 : ℝ) (67/320 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e1 : (((175636480 : ℤ) : ℝ) / (D : ℝ)) = (67/320 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_173015040_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:37:40.705414+00:00
-- url     : https://prove2.me/submissions/3542fc6e-0d0e-4cee-8f56-21ca543ebde4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 33/160]`, `ρ ∈ [147/640, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 169082880 192675840 195461120 ⟨⟨96726665644, 96726665653⟩, ⟨92927897348, 100578213417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 167772160 169082880 195461120 198246400 ⟨⟨98011071705, 98011071713⟩, ⟨94203576829, 101871319747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 169082880 170393600 192675840 195461120 ⟨⟨95934852244, 95934852253⟩, ⟨92157714038, 99764292163⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 169082880 170393600 195461120 198246400 ⟨⟨97210233034, 97210233041⟩, ⟨93424395910, 101048348135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 167772160 169082880 198246400 201031680 ⟨⟨99293018350, 99293018356⟩, ⟨95476825438, 103161937630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 167772160 169082880 201031680 203816960 ⟨⟨100572522671, 100572522677⟩, ⟨96747660019, 104450084402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 169082880 170393600 198246400 201031680 ⟨⟨98483205916, 98483205924⟩, ⟨94688697617, 102329967974⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 169082880 170393600 201031680 203816960 ⟨⟨99753787491, 99753787499⟩, ⟨95950635525, 103609168516⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 170393600 171704320 192675840 195461120 ⟨⟨95149606745, 95149606753⟩, ⟨91393828152, 98957216964⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 170393600 171704320 195461120 198246400 ⟨⟨96416005492, 96416005501⟩, ⟨92651556130, 100232265244⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 171704320 173015040 192675840 195461120 ⟨⟨94370817195, 94370817203⟩, ⟨90636132813, 98156870626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 171704320 173015040 195461120 198246400 ⟨⟨95628276750, 95628276757⟩, ⟨91884950208, 99422953528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 170393600 171704320 198246400 201031680 ⟨⟨97680046858, 97680046864⟩, ⟨93906953683, 101504928705⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 170393600 171704320 201031680 203816960 ⟨⟨98941746964, 98941746970⟩, ⟨95160036710, 102775223696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 171704320 173015040 198246400 201031680 ⟨⟨96883428481, 96883428489⟩, ⟨93131485969, 100686701944⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 171704320 173015040 201031680 203816960 ⟨⟨98136288051, 98136288058⟩, ⟨94375755542, 101948131748⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 173015040 192675840 203816960 t = true :=
  ⟨_, (join_su (m := 170393600) (by decide) (join_sr (m := 198246400) (by decide) (join_su (m := 169082880) (by decide) (join_sr (m := 195461120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 195461120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 169082880) (by decide) (join_sr (m := 201031680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 201031680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 198246400) (by decide) (join_su (m := 171704320) (by decide) (join_sr (m := 195461120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 195461120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 171704320) (by decide) (join_sr (m := 201031680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 201031680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (33/160 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

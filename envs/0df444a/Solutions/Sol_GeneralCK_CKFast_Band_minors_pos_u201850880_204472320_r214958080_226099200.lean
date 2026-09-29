-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u201850880_204472320_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:26:07.749416+00:00
-- url     : https://prove2.me/submissions/78e77abf-15ed-4471-9699-39f06f1418d9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [77/320, 39/160]`, `ρ ∈ [41/160, 69/256]` by 12 cells of the computing
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
theorem cell0 : cellOK 201850880 202506240 214958080 217743360 ⟨⟨86658857064, 86658857070⟩, ⟨84633755007, 88699579697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 202506240 203161600 214958080 217743360 ⟨⟨86300050681, 86300050689⟩, ⟨84280634929, 88335020491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 201850880 202506240 217743360 220528640 ⟨⟨87712677839, 87712677847⟩, ⟨85683310416, 89757665006⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 202506240 203161600 217743360 220528640 ⟨⟨87349974150, 87349974158⟩, ⟨85326302089, 89389199700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 203161600 203816960 214958080 217743360 ⟨⟨85942395575, 85942395582⟩, ⟨83928637512, 87971641622⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 203816960 204472320 214958080 217743360 ⟨⟨85585883028, 85585883034⟩, ⟨83577754272, 87609434142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 203161600 203816960 217743360 220528640 ⟨⟨86988429042, 86988429050⟩, ⟨84970423759, 89021922002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 203816960 204472320 217743360 220528640 ⟨⟨86628033767, 86628033775⟩, ⟨84615666908, 88655822934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 201850880 203161600 220528640 223313920 ⟨⟨88581718569, 88581718575⟩, ⟨85190500446, 92015609378⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 201850880 203161600 223313920 226099200 ⟨⟨89630930868, 89630930875⟩, ⟨86231932007, 93072619876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 203161600 204472320 220528640 223313920 ⟨⟨87850875547, 87850875554⟩, ⟨84475950018, 91268163569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 203161600 204472320 223313920 226099200 ⟨⟨88892366403, 88892366410⟩, ⟨85509690080, 92317423916⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 201850880 204472320 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 203161600) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 202506240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 202506240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 217743360) (by decide) (join_su (m := 203816960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 203816960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 203161600) (by decide) (join_sr (m := 223313920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 223313920) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (77/320 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

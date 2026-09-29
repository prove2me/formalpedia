-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u149422080_152043520_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:31:41.771774+00:00
-- url     : https://prove2.me/submissions/4f1dceac-cd99-4ed4-a347-64b515b8079a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [57/320, 29/160]`, `ρ ∈ [109/640, 59/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 149422080 150077440 142868480 145817600 ⟨⟨82894298542, 82894298550⟩, ⟨80372787447, 85440824186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 150077440 150732800 142868480 145817600 ⟨⟨82536349586, 82536349594⟩, ⟨80023975677, 85073585261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 149422080 150077440 145817600 148766720 ⟨⟨84463065586, 84463065595⟩, ⟨81935642697, 87015459373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 150077440 150732800 145817600 148766720 ⟨⟨84099267670, 84099267676⟩, ⟨81580993768, 86642360691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 150732800 151388160 142868480 145817600 ⟨⟨82180259816, 82180259824⟩, ⟨79676958275, 84708271812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 151388160 152043520 142868480 145817600 ⟨⟨81826010822, 81826010830⟩, ⟨79331717550, 84344864697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 150732800 151388160 145817600 148766720 ⟨⟨83737349170, 83737349177⟩, ⟨81228159553, 86271207588⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 151388160 152043520 145817600 148766720 ⟨⟨83377291553, 83377291562⟩, ⟨80877122235, 85901980798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 149422080 150077440 148766720 151715840 ⟨⟨86027552333, 86027552342⟩, ⟨83494255880, 88585775848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 150077440 150732800 148766720 151715840 ⟨⟨85657952231, 85657952238⟩, ⟨83133816042, 88206864711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 149422080 150077440 151715840 154664960 ⟨⟨87587795305, 87587795312⟩, ⟨85048663064, 90151810590⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 150077440 150732800 151715840 154664960 ⟨⟨87212439227, 87212439233⟩, ⟨84682478010, 89767133728⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 150732800 151388160 148766720 151715840 ⟨⟨85290251276, 85290251284⟩, ⟨82775210770, 87829918748⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 151388160 152043520 148766720 151715840 ⟨⟨84924430812, 84924430820⟩, ⟨82418422117, 87454918572⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 150732800 151388160 151715840 154664960 ⟨⟨86839001532, 86839001538⟩, ⟨84318146882, 89384441129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 151388160 152043520 151715840 154664960 ⟨⟨86467463447, 86467463454⟩, ⟨83955651615, 89003713298⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 149422080 152043520 142868480 154664960 t = true :=
  ⟨_, (join_sr (m := 148766720) (by decide) (join_su (m := 150732800) (by decide) (join_sr (m := 145817600) (by decide) (join_su (m := 150077440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 150077440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 145817600) (by decide) (join_su (m := 151388160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 151388160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 150732800) (by decide) (join_sr (m := 151715840) (by decide) (join_su (m := 150077440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 150077440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 151715840) (by decide) (join_su (m := 151388160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 151388160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (57/320 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((149422080 : ℤ) : ℝ) / (D : ℝ)) = (57/320 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

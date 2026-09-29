-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_251658240_r337510400_348651520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:50:02.432754+00:00
-- url     : https://prove2.me/submissions/b29047a9-1bfd-4d0b-9fa3-00e008bb14d0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 3/10]`, `ρ ∈ [103/256, 133/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247726080 337510400 340295680 ⟨⟨99120997548, 99120997554⟩, ⟨95921747105, 102356080933⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246415360 247726080 340295680 343080960 ⟨⟨99899530675, 99899530682⟩, ⟨96693631937, 103141300701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247726080 249036800 337510400 340295680 ⟨⟨98236460194, 98236460200⟩, ⟨95050148709, 101458425431⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247726080 249036800 340295680 343080960 ⟨⟨99008651855, 99008651861⟩, ⟨95815717077, 102237279369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 246415360 247726080 343080960 345866240 ⟨⟨100677583761, 100677583768⟩, ⟨97465037903, 103926039098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246415360 247726080 345866240 348651520 ⟨⟨101455159166, 101455159172⟩, ⟨98235967347, 104710298493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247726080 249036800 343080960 345866240 ⟨⟨99780375285, 99780375290⟩, ⟨96580818229, 103015663905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247726080 249036800 345866240 348651520 ⟨⟨100551632772, 100551632777⟩, ⟨97345454446, 103793581339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 250347520 337510400 340295680 ⟨⟨97355345522, 97355345528⟩, ⟨94181873093, 100564294238⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249036800 250347520 340295680 343080960 ⟨⟨98121204991, 98121204998⟩, ⟨94941134439, 101336791435⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 250347520 251658240 337510400 340295680 ⟨⟨96477608676, 96477608684⟩, ⟨93316876617, 99673641260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 250347520 251658240 340295680 343080960 ⟨⟨97237145180, 97237145187⟩, ⟨94069840330, 100439790762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249036800 250347520 343080960 345866240 ⟨⟨98886607820, 98886607825⟩, ⟨95699940008, 102108830976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 249036800 250347520 345866240 348651520 ⟨⟨99651556229, 99651556236⟩, ⟨96458292012, 102880415096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 250347520 251658240 343080960 345866240 ⟨⟨97996236418, 97996236426⟩, ⟨94822359494, 101205494140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250347520 251658240 345866240 348651520 ⟨⟨98754884551, 98754884558⟩, ⟨95574436258, 101970753559⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 251658240 337510400 348651520 t = true :=
  ⟨_, (join_su (m := 249036800) (by decide) (join_sr (m := 343080960) (by decide) (join_su (m := 247726080) (by decide) (join_sr (m := 340295680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 340295680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 247726080) (by decide) (join_sr (m := 345866240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 345866240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 343080960) (by decide) (join_su (m := 250347520) (by decide) (join_sr (m := 340295680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 340295680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 250347520) (by decide) (join_sr (m := 345866240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 345866240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (103/256 : ℝ) (133/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((337510400 : ℤ) : ℝ) / (D : ℝ)) = (103/256 : ℝ) := by norm_num [D]
  have e3 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

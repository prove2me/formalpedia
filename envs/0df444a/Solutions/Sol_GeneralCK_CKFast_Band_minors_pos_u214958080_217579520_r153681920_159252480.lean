-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_217579520_r153681920_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:36:02.207543+00:00
-- url     : https://prove2.me/submissions/b9ad59d8-9c88-47be-9ff4-0b4dd47dc117

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 83/320]`, `ρ ∈ [469/2560, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 214958080 215613440 153681920 155074560 ⟨⟨57659762634, 57659762641⟩, ⟨56127234301, 59202054334⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 214958080 215613440 155074560 156467200 ⟨⟨58161190993, 58161191000⟩, ⟨56626737669, 59705412028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 215613440 216268800 153681920 155074560 ⟨⟨57409372513, 57409372519⟩, ⟨55880340341, 58948131242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 215613440 216268800 155074560 156467200 ⟨⟨57908772291, 57908772296⟩, ⟨56377820154, 59449455379⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 214958080 215613440 156467200 157859840 ⟨⟨58662317488, 58662317493⟩, ⟨57125940320, 60208466694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 214958080 215613440 157859840 159252480 ⟨⟨59163142923, 59163142929⟩, ⟨57624843058, 60711219137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 215613440 216268800 156467200 157859840 ⟨⟨58407873795, 58407873802⟩, ⟨56875002817, 59950480103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 215613440 216268800 157859840 159252480 ⟨⟨58906677820, 58906677825⟩, ⟨57371889118, 60451206210⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 216268800 216924160 153681920 155074560 ⟨⟨57159792501, 57159792507⟩, ⟨55634237985, 58695037028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 216268800 216924160 155074560 156467200 ⟨⟨57657168507, 57657168512⟩, ⟨56129699043, 59194332422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 216924160 217579520 153681920 155074560 ⟨⟨56911016306, 56911016313⟩, ⟨55388921084, 58442765250⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 216924160 217579520 155074560 156467200 ⟨⟨57406373316, 57406373322⟩, ⟨55882368159, 58940036685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 216268800 216924160 156467200 157859840 ⟨⟨58154249792, 58154249798⟩, ⟨56624866480, 59693331983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 216268800 216924160 157859840 159252480 ⟨⟨58651037139, 58651037144⟩, ⟨57119741074, 60192036493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 216924160 217579520 156467200 157859840 ⟨⟨57901439124, 57901439130⟩, ⟨56375525106, 59437015829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 216924160 217579520 157859840 159252480 ⟨⟨58396214500, 58396214505⟩, ⟨56868392690, 59933703453⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 217579520 153681920 159252480 t = true :=
  ⟨_, (join_su (m := 216268800) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 215613440) (by decide) (join_sr (m := 155074560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 155074560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 215613440) (by decide) (join_sr (m := 157859840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 157859840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 156467200) (by decide) (join_su (m := 216924160) (by decide) (join_sr (m := 155074560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 155074560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 216924160) (by decide) (join_sr (m := 157859840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 157859840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (83/320 : ℝ) →
    rho ∈ Set.Icc (469/2560 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e2 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

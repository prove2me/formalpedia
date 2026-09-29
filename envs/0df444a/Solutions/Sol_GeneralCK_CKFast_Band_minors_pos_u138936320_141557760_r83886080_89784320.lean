-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u138936320_141557760_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:07:58.916595+00:00
-- url     : https://prove2.me/submissions/1d73d851-d0d0-43bc-80e2-f5d83b779c06

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [53/320, 27/160]`, `ρ ∈ [1/10, 137/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 138936320 139591680 83886080 85360640 ⟨⟨53991636055, 53991636059⟩, ⟨51976072538, 56025158268⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 138936320 139591680 85360640 86835200 ⟨⟨54882210880, 54882210883⟩, ⟨52863516914, 56918851792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 139591680 140247040 83886080 85360640 ⟨⟨53739867231, 53739867240⟩, ⟨51731471606, 55766102853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 139591680 140247040 85360640 86835200 ⟨⟨54626683393, 54626683401⟩, ⟨52615167861, 56656027538⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 138936320 139591680 86835200 88309760 ⟨⟨55771231605, 55771231608⟩, ⟨53749419041, 57810979304⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 138936320 139591680 88309760 89784320 ⟨⟨56658705821, 56658705824⟩, ⟨54633786426, 58701548467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 139591680 140247040 86835200 88309760 ⟨⟨55511963993, 55511964001⟩, ⟨53497340218, 57544404929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 139591680 140247040 88309760 89784320 ⟨⟨56395716489, 56395716496⟩, ⟨54377996056, 58431242563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 140247040 140902400 83886080 85360640 ⟨⟨53489682063, 53489682069⟩, ⟨51488395125, 55508691630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 140247040 140902400 85360640 86835200 ⟨⟨54372758603, 54372758611⟩, ⟨52368362280, 56394866529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 140902400 141557760 83886080 85360640 ⟨⟨53241062468, 53241062477⟩, ⟨51246825766, 55252905757⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 140902400 141557760 85360640 86835200 ⟨⟨54120418255, 54120418263⟩, ⟨52123082665, 56135349751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 140247040 140902400 86835200 88309760 ⟨⟨55254317885, 55254317892⟩, ⟨53246823658, 57279512621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 140247040 140902400 88309760 89784320 ⟨⟨56134367236, 56134367242⟩, ⟨54123786507, 58162637307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 140902400 141557760 86835200 88309760 ⟨⟨54998274854, 54998274862⟩, ⟨52997851679, 57016283189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 140902400 141557760 88309760 89784320 ⟨⟨55874639467, 55874639473⟩, ⟨53871139933, 57895713345⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 138936320 141557760 83886080 89784320 t = true :=
  ⟨_, (join_su (m := 140247040) (by decide) (join_sr (m := 86835200) (by decide) (join_su (m := 139591680) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 85360640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 139591680) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 88309760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 86835200) (by decide) (join_su (m := 140902400) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 85360640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 140902400) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 88309760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (53/320 : ℝ) (27/160 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((138936320 : ℤ) : ℝ) / (D : ℝ)) = (53/320 : ℝ) := by norm_num [D]
  have e1 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

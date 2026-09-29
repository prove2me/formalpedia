-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u112721920_115343360_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:05:51.510778+00:00
-- url     : https://prove2.me/submissions/9ac2c3fd-dce3-45d8-8878-6c10b9a8bbf1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/320, 11/80]`, `ρ ∈ [137/1280, 73/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 112721920 113377280 89784320 91258880 ⟨⟨69829479311, 69829479313⟩, ⟨67454121740, 72228801663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 112721920 113377280 91258880 92733440 ⟨⟨70878256257, 70878256261⟩, ⟨68499432323, 73281010174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 113377280 114032640 89784320 91258880 ⟨⟨69476996954, 69476996961⟩, ⟨67112010024, 71865756764⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 113377280 114032640 91258880 92733440 ⟨⟨70521207755, 70521207762⟩, ⟨68152763211, 72913391217⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 112721920 113377280 92733440 94208000 ⟨⟨71924557684, 71924557687⟩, ⟨69542288772, 74330721723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 112721920 113377280 94208000 95682560 ⟨⟨72968398698, 72968398702⟩, ⟨70582705993, 75377951616⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 113377280 114032640 92733440 94208000 ⟨⟨71562973584, 71562973594⟩, ⟨69191092483, 73958559587⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 113377280 114032640 94208000 95682560 ⟨⟨72602309277, 72602309286⟩, ⟨70227012480, 75001276895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 114032640 114688000 89784320 91258880 ⟨⟨69127236482, 69127236489⟩, ⟨66772517082, 71505539422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 114032640 114688000 91258880 92733440 ⟨⟨70166907462, 70166907469⟩, ⟨67808739280, 72548626044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 114688000 115343360 89784320 91258880 ⟨⟨68780161443, 68780161450⟩, ⟨66435608020, 71148111589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 114688000 115343360 91258880 92733440 ⟨⟨69815318677, 69815318686⟩, ⟨67467325382, 72186676358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 114032640 114688000 92733440 94208000 ⟨⟨71204163601, 71204163610⟩, ⟨68842567370, 73589277033⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 114032640 114688000 94208000 95682560 ⟨⟨72239019459, 72239019468⟩, ⟨69874015724, 74627507136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 114688000 115343360 92733440 94208000 ⟨⟨70848090785, 70848090792⟩, ⟨68496678031, 73222835523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 114688000 115343360 94208000 95682560 ⟨⟨71878492060, 71878492067⟩, ⟨69523680077, 74256603566⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 112721920 115343360 89784320 95682560 t = true :=
  ⟨_, (join_su (m := 114032640) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 113377280) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 91258880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 113377280) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 94208000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 92733440) (by decide) (join_su (m := 114688000) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 91258880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 114688000) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 94208000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/320 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((112721920 : ℤ) : ℝ) / (D : ℝ)) = (43/320 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

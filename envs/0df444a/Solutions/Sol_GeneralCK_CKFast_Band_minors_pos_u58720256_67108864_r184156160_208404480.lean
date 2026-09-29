-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u58720256_67108864_r184156160_208404480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:15:08.12584+00:00
-- url     : https://prove2.me/submissions/a63d2207-4c83-4931-baf5-7430d4a5bb28

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/100, 2/25]`, `ρ ∈ [281/1280, 159/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 58720256 60817408 184156160 190218240 ⟨⟨201026369313, 201026369325⟩, ⟨187710867683, 214839949451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 58720256 60817408 190218240 196280320 ⟨⟨205846318533, 205846318544⟩, ⟨192531188351, 219649970441⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 60817408 62914560 184156160 190218240 ⟨⟨197389356081, 197389356092⟩, ⟨184346836217, 210914337884⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 60817408 62914560 190218240 196280320 ⟨⟨202167386994, 202167387009⟩, ⟨189121962702, 215686351925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 58720256 60817408 196280320 202342400 ⟨⟨210601560247, 210601560261⟩, ⟨197287997456, 224394302467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 58720256 60817408 202342400 208404480 ⟨⟨215294333355, 215294333370⟩, ⟨201983442394, 229075270021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 60817408 62914560 196280320 202342400 ⟨⟨206882761816, 206882761828⟩, ⟨193835639206, 220394694363⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 60817408 62914560 202342400 208404480 ⟨⟨211537604645, 211537604657⟩, ⟨198489902252, 225041571976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 62914560 65011712 184156160 190218240 ⟨⟨193868162125, 193868162137⟩, ⟨181087273527, 207116660396⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 62914560 65011712 190218240 196280320 ⟨⟨198603798222, 198603798233⟩, ⟨185817018321, 211849853904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 65011712 67108864 184156160 190218240 ⟨⟨190456613336, 190456613348⟩, ⟨177926705215, 203439994169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 65011712 67108864 190218240 196280320 ⟨⟨195149478051, 195149478062⟩, ⟨182610954559, 208133683993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 62914560 65011712 196280320 202342400 ⟨⟨203278771936, 203278771950⟩, ⟨190487310188, 216521344938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 62914560 65011712 202342400 208404480 ⟨⟨207895098718, 207895098730⟩, ⟨195100080900, 221133228558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 65011712 67108864 196280320 202342400 ⟨⟨199783616526, 199783616537⟩, ⟨187237684690, 212767590993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 65011712 67108864 202342400 208404480 ⟨⟨204360941370, 204360941384⟩, ⟨191808728409, 217343704247⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 58720256 67108864 184156160 208404480 t = true :=
  ⟨_, (join_su (m := 62914560) (by decide) (join_sr (m := 196280320) (by decide) (join_su (m := 60817408) (by decide) (join_sr (m := 190218240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 190218240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 60817408) (by decide) (join_sr (m := 202342400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 202342400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 196280320) (by decide) (join_su (m := 65011712) (by decide) (join_sr (m := 190218240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 190218240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 65011712) (by decide) (join_sr (m := 202342400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 202342400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/100 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (281/1280 : ℝ) (159/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  have e3 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_125829120_r508559360_555745280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:46:57.863044+00:00
-- url     : https://prove2.me/submissions/933783ae-9f5a-4875-b9f5-c857b3ab5de6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 3/20]`, `ρ ∈ [97/160, 53/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 115343360 117964800 508559360 520355840 ⟨⟨301672572188, 301672572200⟩, ⟨287647203631, 316033068397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 117964800 120586240 508559360 520355840 ⟨⟨297730610614, 297730610625⟩, ⟨283868974853, 311924603958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 115343360 117964800 520355840 532152320 ⟨⟨307099288467, 307099288479⟩, ⟨293037338011, 321490023589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 117964800 120586240 520355840 532152320 ⟨⟨303119966167, 303119966179⟩, ⟨289219805415, 317346420207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 120586240 123207680 508559360 520355840 ⟨⟨293839406040, 293839406050⟩, ⟨280138558634, 307869828857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 123207680 125829120 508559360 520355840 ⟨⟨289997463767, 289997463771⟩, ⟨276454546883, 303867165101⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 120586240 123207680 520355840 532152320 ⟨⟨299190773012, 299190773024⟩, ⟨285449564975, 313255761596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 123207680 125829120 520355840 532152320 ⟨⟨295310246730, 295310246738⟩, ⟨281725236409, 309216507095⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 115343360 117964800 532152320 543948800 ⟨⟨312491742698, 312491742710⟩, ⟨298393883145, 326912087350⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 117964800 120586240 532152320 543948800 ⟨⟨308475911138, 308475911151⟩, ⟨294537901990, 322734185916⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 115343360 117964800 543948800 555745280 ⟨⟨317851191134, 317851191146⟩, ⟨303718056010, 332300553411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 117964800 120586240 543948800 555745280 ⟨⟨313799658166, 313799658177⟩, ⟨299824438991, 328089150394⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 120586240 123207680 532152320 543948800 ⟨⟨304509572623, 304509572635⟩, ⟨290728681972, 318608479329⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 123207680 125829120 532152320 543948800 ⟨⟨300591296641, 300591296648⟩, ⟨286964870164, 314533463341⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 120586240 123207680 543948800 555745280 ⟨⟨309796975046, 309796975057⟩, ⟨295977042660, 323929188014⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 123207680 125829120 543948800 555745280 ⟨⟨305841742352, 305841742361⟩, ⟨292174540971, 319819197554⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 125829120 508559360 555745280 t = true :=
  ⟨_, (join_sr (m := 532152320) (by decide) (join_su (m := 120586240) (by decide) (join_sr (m := 520355840) (by decide) (join_su (m := 117964800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 117964800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 520355840) (by decide) (join_su (m := 123207680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 123207680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 120586240) (by decide) (join_sr (m := 543948800) (by decide) (join_su (m := 117964800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 117964800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 543948800) (by decide) (join_su (m := 123207680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 123207680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (97/160 : ℝ) (53/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((508559360 : ℤ) : ℝ) / (D : ℝ)) = (97/160 : ℝ) := by norm_num [D]
  have e3 : (((555745280 : ℤ) : ℝ) / (D : ℝ)) = (53/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1

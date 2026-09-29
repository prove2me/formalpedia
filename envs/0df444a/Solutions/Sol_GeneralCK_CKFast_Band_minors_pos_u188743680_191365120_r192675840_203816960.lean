-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_191365120_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:05:46.99306+00:00
-- url     : https://prove2.me/submissions/a0019ba2-2781-4ccc-aa12-fa41831c462a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 73/320]`, `ρ ∈ [147/640, 311/1280]` by 15 cells of the computing
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
theorem cell0 : cellOK 188743680 189399040 192675840 195461120 ⟨⟨84962784228, 84962784235⟩, ⟨82853491131, 87089181770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 189399040 190054400 192675840 195461120 ⟨⟨84612055748, 84612055754⟩, ⟨82509001390, 86732135260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 188743680 189399040 195461120 198246400 ⟨⟨86109861469, 86109861475⟩, ⟨83996037487, 88240783802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 189399040 190054400 195461120 198246400 ⟨⟨85754934090, 85754934098⟩, ⟨83647358480, 87879529112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 190054400 190709760 192675840 195461120 ⟨⟨84262601156, 84262601164⟩, ⟨82165751418, 86376397346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 190709760 191365120 192675840 195461120 ⟨⟨83914410251, 83914410258⟩, ⟨81823731305, 86021957523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 190054400 190709760 195461120 198246400 ⟨⟨85401289974, 85401289982⟩, ⟨83299928651, 87519592347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 190709760 191365120 195461120 198246400 ⟨⟨85048918866, 85048918873⟩, ⟨82953738040, 87160962955⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 188743680 189399040 198246400 201031680 ⟨⟨87255185788, 87255185794⟩, ⟨85136842778, 89390620936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 189399040 190054400 198246400 201031680 ⟨⟨86896078620, 86896078626⟩, ⟨84783993431, 89025177359⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 188743680 190054400 201031680 203816960 ⟨⟨88216970635, 88216970642⟩, ⟨84709793915, 91770137821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 190054400 190709760 198246400 201031680 ⟨⟨86538263901, 86538263907⟩, ⟨84432402487, 88661060848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 190709760 191365120 198246400 201031680 ⟨⟨86181731334, 86181731340⟩, ⟨84082059945, 88298260808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 190054400 190709760 201031680 203816960 ⟨⟨87673533411, 87673533418⟩, ⟨85563183314, 89800813406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 190709760 191365120 201031680 203816960 ⟨⟨87312857975, 87312857981⟩, ⟨85208707254, 89433861488⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 191365120 192675840 203816960 t = true :=
  ⟨_, (join_sr (m := 198246400) (by decide) (join_su (m := 190054400) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 189399040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 189399040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 195461120) (by decide) (join_su (m := 190709760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 190709760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 190054400) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 189399040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 201031680) (by decide) (join_su (m := 190709760) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 190709760) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (73/320 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((191365120 : ℤ) : ℝ) / (D : ℝ)) = (73/320 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
